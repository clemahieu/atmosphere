// SPDX-License-Identifier: MIT

//! Deriving a capability, the only way to share one: the child's rights and range lie within its
//! parent's and its depth is one greater, so whoever derived it can always revoke it. The child goes
//! in a free slot of the caller's table, or of the table of a process the caller controls, which is
//! a grant through control. See design/sharing-by-derive/ and design/process-holds-capabilities/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
#[cfg(verus_keep_ghost)]
use vstd::bits::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::endpoint::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reply::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
use crate::capability::refs::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;

/// The child a derive from `parent` makes. A core capability's names one page, so its order is 0, and
/// the derive's order is the child's maximum priority instead. See design/cpu-time-as-capability/.
pub open spec fn child_of(parent: Payload, rights: u32, base: usize, order: u8) -> Payload {
    if parent.kind is Core {
        Payload { kind: parent.kind, order: 0, rights, base, badge: parent.badge, priority: order as usize }
    } else {
        Payload { kind: parent.kind, order, rights, base, badge: parent.badge, priority: 0 }
    }
}

/// A derive may set this badge on a child of parent: 0, which keeps the parent's, or one that fits 48
/// bits on a child of an endpoint's capability whose own badge is 0. A badge, once set, is in every
/// capability derived below it, as badges_inherited states, so a receiver can tell which lineage a
/// sender holds.
pub open spec fn badge_allowed(parent: Payload, badge: usize) -> bool {
    ||| badge == 0
    ||| parent.kind is Endpoint && parent.badge == 0 && badge < BADGE_LIMIT
}

/// The child a derive with this badge makes: child_of, with the badge when it is not 0.
pub open spec fn badged_child_of(parent: Payload, rights: u32, base: usize, order: u8, badge: usize) -> Payload {
    let c = child_of(parent, rights, base, order);
    if badge == 0 {
        c
    } else {
        Payload { kind: c.kind, order: c.order, rights: c.rights, base: c.base, badge, priority: c.priority }
    }
}

/// A child of an endpoint's capability with a badge is an endpoint's capability with that badge.
pub open spec fn badge_kept(parent: Payload, child: Payload) -> bool {
    parent.kind is Endpoint && parent.badge != 0 ==> child.kind is Endpoint && child.badge == parent.badge
}

/// Node x keeps its parent's badge, when its parent is a capability.
pub open spec fn badge_kept_at(list: &Tree, tables: &Tables, x: usize) -> bool {
    list.parent@.contains_key(x) && tables.is_cap(list, list.parent@[x])
        ==> badge_kept(tables.payload_of(list.parent@[x]), tables.payload_of(x))
}

/// Every capability keeps its parent's badge, so a badge, once set, is in every capability below the
/// one it was set on. Opaque, as binding_parents is, so that its node quantifier does not chain into
/// the tables in every proof that mentions a capability.
#[verifier::opaque]
pub open spec fn badges_inherited(list: &Tree, tables: &Tables) -> bool {
    forall|x: usize| #[trigger] tables.is_cap(list, x) ==> badge_kept_at(list, tables, x)
}

/// A block of this order at this base is a whole block lying within the parent's.
pub open spec fn block_within(base: usize, order: u8, parent: Payload) -> bool {
    &&& order <= parent.order
    &&& parent.base <= base
    &&& base as int % block_bytes(order) == 0
    &&& base as int + block_bytes(order) <= parent.base as int + block_bytes(parent.order)
}

/// The child's rights and block lie within the parent's. Only a block of memory can be narrowed: any
/// other object is its block's base. And control reads a capability's name alone, so a child that
/// keeps control keeps the parent's block. A core capability's child allows no higher a priority.
pub open spec fn narrows(child: Payload, parent: Payload) -> bool {
    &&& child.rights & !parent.rights == 0
    &&& block_within(child.base, child.order, parent)
    &&& (child.base != parent.base || child.order != parent.order) ==> {
        &&& parent.kind is Untyped || parent.kind is Frame
        &&& child.rights & right_bit(Right::Control) == 0
    }
    &&& parent.kind is Core ==> child.priority <= parent.priority
}

/// A block of this order, in bytes, in constant time.
pub fn order_bytes(order: u8) -> (ret: usize)
    requires
        order <= MAX_ORDER,
    ensures
        ret as int == block_bytes(order),
        0 < ret <= NODE_SPACE,
{
    proof {
        lemma_pow2_pos(order as nat);
        lemma_pow2_order(order);
        lemma_usize_shl_is_mul(PAGE_SZ, order as usize);
    }
    PAGE_SZ << (order as usize)
}

/// A block of any order fits in the address space.
proof fn lemma_pow2_order(order: u8)
    requires
        order <= MAX_ORDER,
    ensures
        pow2(order as nat) * PAGE_SZ <= NODE_SPACE,
{
    lemma2_to64_rest();
    if order < MAX_ORDER {
        lemma_pow2_strictly_increases(order as nat, MAX_ORDER as nat);
    }
}

/// Decides whether a block lies within a capability's, in constant time. Base and order come from
/// user space.
pub fn is_block_within(parent: Payload, base: usize, order: u8) -> (ret: bool)
    requires
        payload_wf(parent),
    ensures
        ret == block_within(base, order, parent),
        ret ==> order <= MAX_ORDER,
        ret ==> base as int % block_bytes(order) == 0,
        ret ==> base as int + block_bytes(order) <= NODE_SPACE as int,
{
    if order > parent.order || base < parent.base || base >= NODE_SPACE {
        proof {
            lemma_pow2_pos(order as nat);
        }
        return false;
    }
    let size = order_bytes(order);
    let parent_size = order_bytes(parent.order);
    base + size <= parent.base + parent_size && base % size == 0
}

/// A block lies within a one-page parent's only as that page: so a child of a console or a power
/// capability, whose object is a page past memory, names its parent's object.
proof fn lemma_object_within(parent: Payload, base: usize, order: u8)
    requires
        parent.order == 0,
        parent.base % PAGE_SZ == 0,
    ensures
        block_within(base, order, parent) <==> (order == 0 && base == parent.base),
{
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(block_bytes(0) == PAGE_SZ);
}

/// Decides whether a child with these fields may be derived from `parent`, in constant time. All of
/// rights, base and order come from user space.
fn may_derive(parent: Payload, rights: u32, base: usize, order: u8) -> (ret: bool)
    requires
        payload_wf(parent),
        !(parent.kind is Core),
    ensures
        ret <==> narrows(child_of(parent, rights, base, order), parent),
        ret ==> payload_wf(child_of(parent, rights, base, order)),
{
    if rights & !parent.rights != 0 || !is_block_within(parent, base, order) {
        return false;
    }
    if base != parent.base || order != parent.order {
        let block = match parent.kind {
            CapKind::Untyped | CapKind::Frame => true,
            _ => false,
        };
        if !block || rights & 128 != 0 {
            return false;
        }
    }
    true
}

impl CapKernel {
    /// The refusals of a derive from index from of the table at src into index to of the table at dst:
    /// an index that names no slot, a parent that is no capability, a device's, a notification's, a
    /// reply's, a dead process's or thread's, or at the deepest depth, a child's slot in use, a child that does not
    /// narrow its parent, a badge badge_allowed refuses, or a block that counts its holders and has no room for
    /// one more. A console's, power's or endpoint's child names its parent's object, with rights no
    /// wider, and so does a core capability's, with a maximum priority, the order, no higher.
    pub open spec fn can_derive_between(&self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8, badge: usize) -> bool {
        let parent = self.tables.node_of(src, from);
        let child = self.tables.node_of(dst, to);
        &&& self.tables.has_slot(&self.list, src, from)
        &&& self.tables.has_slot(&self.list, dst, to)
        &&& self.is_cap(parent)
        &&& !(self.payload_of(parent).kind is Device)
        &&& !(self.payload_of(parent).kind is Notification)
        &&& !(self.payload_of(parent).kind is Reply)
        &&& !self.cap_dead(parent)
        &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
        &&& !self.list.nodes@[child as int].live
        &&& narrows(child_of(self.payload_of(parent), rights, base, order), self.payload_of(parent))
        &&& badge_allowed(self.payload_of(parent), badge)
        &&& tracked_kind(self.payload_of(parent).kind) ==>
            block_refs(&self.blocks, block_ref(&self.blocks, self.payload_of(parent).base / PAGE_SZ)) != usize::MAX
    }

    /// The refusals of a derive from index from of the caller's table, at root, into a position: one
    /// in no table, or in the table of a dead process, to which nothing is given since it cannot use
    /// it, and then a derive's between the two tables.
    pub open spec fn can_derive_at(&self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8, badge: usize) -> bool {
        let dst = self.table_at(root, to.through);
        &&& dst is Some
        &&& to.through is Some ==> !self.processes.records@[dst->0].value().dead
        &&& self.can_derive_between(root, from, dst->0, to.index, rights, base, order, badge)
    }

    /// What a derive from the capability at index from of the table at src into the empty index to of
    /// the table at dst did: the derive was allowed, and the child, in dst's table, holds the parent's
    /// kind with these rights and this block, which narrow the parent's, and the badge, or the parent's
    /// when it is 0, one depth below it as its child.
    pub open spec fn cap_derived_between(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8, badge: usize) -> bool {
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        &&& pre.can_derive_between(src, from, dst, to, rights, base, order, badge)
        &&& pre.view().holds(src, parent)
        &&& post.view().holds(dst, child)
        &&& !pre.list.nodes@[child as int].live
        &&& narrows(post.payload_of(child), pre.payload_of(parent))
        &&& post.payload_of(child) == badged_child_of(pre.payload_of(parent), rights, base, order, badge)
        &&& post.list.is_child(parent, child)
        &&& post.list.nodes@[child as int].depth == pre.list.nodes@[parent as int].depth + 1
        &&& post.list.nodes@[child as int].depth <= MAX_DEPTH
    }

    /// What a derive into a position is to reach: a local step in the caller's own table, and through a
    /// process capability a placement through it of a child of the caller's capability.
    pub open spec fn derive_effect(&self, root: usize, from: usize, to: Position) -> Effect {
        match to.through {
            None => Effect::Local,
            Some(cap) => Effect::Place { cap: self.tables.node_of(root, cap), from: self.tables.node_of(root, from) },
        }
    }

    /// What a derive from the capability at index from of the caller's table, at root, into the empty
    /// position to did: the derive was allowed, the child is in the position's table, every process's record
    /// is as it was, and the step discharges the derive's effect there, a local step in the caller's own
    /// table.
    pub open spec fn cap_derived_at(pre: Self, post: Self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8, badge: usize) -> bool {
        &&& pre.can_derive_at(root, from, to, rights, base, order, badge)
        &&& Self::cap_derived_between(pre, post, root, from, pre.table_at(root, to.through)->0, to.index, rights, base, order, badge)
        &&& discharges(pre.view(), post.view(), root, pre.derive_effect(root, from, to))
        &&& post.processes.records == pre.processes.records
    }

    /// A console or power capability derives a child naming its object, with rights no wider and no
    /// badge, so its holder can pass it on and keep its own, and a core capability one naming its core,
    /// with a maximum priority, the order, no higher than its own; a device's derives nothing, since a
    /// device is bound to one space at a time.
    pub proof fn lemma_console_power_derive(&self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8, badge: usize)
        requires
            self.wf(),
            self.tables.has_slot(&self.list, src, from),
            self.tables.has_slot(&self.list, dst, to),
            self.is_cap(self.tables.node_of(src, from)),
        ensures
            ({
                let parent = self.tables.node_of(src, from);
                let p = self.payload_of(parent);
                (p.kind is Console || p.kind is Power) ==> (self.can_derive_between(src, from, dst, to, rights, base, order, badge) <==> {
                    &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
                    &&& !self.list.nodes@[self.tables.node_of(dst, to) as int].live
                    &&& rights & !p.rights == 0
                    &&& base == p.base
                    &&& order == 0
                    &&& badge == 0
                })
            }),
            ({
                let parent = self.tables.node_of(src, from);
                let p = self.payload_of(parent);
                p.kind is Core ==> (self.can_derive_between(src, from, dst, to, rights, base, order, badge) <==> {
                    &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
                    &&& !self.list.nodes@[self.tables.node_of(dst, to) as int].live
                    &&& rights & !p.rights == 0
                    &&& base == p.base
                    &&& order as usize <= p.priority
                    &&& badge == 0
                })
            }),
            self.payload_of(self.tables.node_of(src, from)).kind is Device
                ==> !self.can_derive_between(src, from, dst, to, rights, base, order, badge),
    {
        let p = self.payload_of(self.tables.node_of(src, from));
        if p.kind is Console || p.kind is Power {
            assert(cap_wf(p));
            lemma_object_within(p, base, order);
        }
        if p.kind is Core {
            assert(cap_wf(p));
            lemma_object_within(p, base, 0);
        }
    }

    /// An endpoint capability derives a child naming its endpoint, with rights no wider, and with a
    /// badge only when its own is 0 and the badge fits 48 bits, while the endpoint's block has room for
    /// one more holder.
    pub proof fn lemma_endpoint_derive(&self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8, badge: usize)
        requires
            self.wf(),
            self.tables.has_slot(&self.list, src, from),
            self.tables.has_slot(&self.list, dst, to),
            self.is_cap(self.tables.node_of(src, from)),
            self.payload_of(self.tables.node_of(src, from)).kind is Endpoint,
        ensures
            ({
                let parent = self.tables.node_of(src, from);
                let p = self.payload_of(parent);
                self.can_derive_between(src, from, dst, to, rights, base, order, badge) <==> {
                    &&& self.list.nodes@[parent as int].depth < MAX_DEPTH
                    &&& !self.list.nodes@[self.tables.node_of(dst, to) as int].live
                    &&& rights & !p.rights == 0
                    &&& base == p.base
                    &&& order == 0
                    &&& badge == 0 || (p.badge == 0 && badge < BADGE_LIMIT)
                    &&& block_refs(&self.blocks, BlockRef::Small(p.base / PAGE_SZ)) != usize::MAX
                }
            }),
    {
        let n = self.tables.node_of(src, from);
        let p = self.payload_of(n);
        self.lemma_endpoint_cap(n);
        lemma_object_within(p, base, order);
    }

    /// What a derive from the capability at node parent does to the block table: the child of a frame,
    /// a space, a thread, a process or an endpoint is one more holder of the block its parent lies in, which had
    /// room for it, and that block's count alone changed; any other child holds no block, and the block
    /// table is as it was.
    pub open spec fn derive_counted(pre: Self, post: Self, parent: usize) -> bool {
        let p = pre.payload_of(parent);
        let br = block_ref(&pre.blocks, p.base / PAGE_SZ);
        if tracked_kind(p.kind) {
            &&& block_refs(&pre.blocks, br) < usize::MAX
            &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
        } else {
            post.blocks == pre.blocks
        }
    }

    /// Derives the capability at index `from` of the caller's table, at `root`, into the empty position
    /// `to`: an index of the caller's table, or of the table of a process the caller controls, which
    /// must not be dead. The index, the position, rights, base, order and badge come from user space,
    /// so any of them can be refused, and a refusal changes nothing.
    pub fn derive(&mut self, root: usize, from: usize, to: Position, rights: u32, base: usize, order: u8, badge: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).tables.roots == old(self).tables.roots,
            ret ==> Self::derive_step(*old(self), *final(self), old(self).tables.node_of(old(self).table_at(root, to.through)->0, to.index)),
            ret && !tracked_kind(old(self).payload_of(old(self).tables.node_of(root, from)).kind) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
                &&& final(self).spaces.holders == old(self).spaces.holders
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
            },
            Self::same_tree(*old(self), *final(self)),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::cap_derived_at(*old(self), *final(self), root, from, to, rights, base, order, badge),
            ret ==> Self::derive_counted(*old(self), *final(self), old(self).tables.node_of(root, from)),
            ret ==> final(self).list.parent@ == old(self).list.parent@.insert(
                old(self).tables.node_of(old(self).table_at(root, to.through)->0, to.index),
                old(self).tables.node_of(root, from),
            ),
            ret ==> final(self).list.seq@[0] == old(self).list.seq@[0],
            ret == old(self).can_derive_at(root, from, to, rights, base, order, badge),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            final(self).endpoints.records == old(self).endpoints.records,
            final(self).threads.records == old(self).threads.records,
            final(self).threads.queues == old(self).threads.queues,
    {
        let ghost pre = *old(self);
        let dst = match self.find_table(root, to.through) {
            Some(table) => table,
            None => { return false; },
        };
        if let Some(cap) = to.through {
            proof {
                pre.lemma_process_cap(pre.tables.node_of(root, cap));
            }
            if self.is_process_dead(dst) {
                return false;
            }
        }
        let ret = self.derive_between(root, from, dst, to.index, rights, base, order, badge);
        if ret {
            proof {
                assert(saved_registers(&self.threads) =~= saved_registers(&pre.threads));
                match to.through {
                    None => {
                        Self::lemma_derive_discharges(pre, *self, root, from, to.index);
                    },
                    Some(cap) => {
                        pre.lemma_slot(root, cap);
                        Self::lemma_derive_into_discharges(pre, *self, root, pre.tables.node_of(root, cap), from, dst, to.index);
                    },
                }
            }
        }
        ret
    }

    /// Derives the capability at index `from` of the table at `src` into the empty index `to` of the
    /// table at `dst`: a derive when they are one table, a placement's step when not. A refusal changes
    /// nothing.
    fn derive_between(&mut self, src: usize, from: usize, dst: usize, to: usize, rights: u32, base: usize, order: u8, badge: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(src),
            old(self).tables.roots@.contains_key(dst),
        ensures
            final(self).frames == old(self).frames,
            final(self).wf(),
            final(self).cores == old(self).cores,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).iommus == old(self).iommus,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            final(self).tables.roots == old(self).tables.roots,
            final(self).devices == old(self).devices,
            final(self).processes.records == old(self).processes.records,
            ret && !tracked_kind(old(self).payload_of(old(self).tables.node_of(src, from)).kind) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
                &&& final(self).spaces.holders == old(self).spaces.holders
                &&& final(self).threads == old(self).threads
                &&& final(self).processes == old(self).processes
            },
            Self::same_tree(*old(self), *final(self)),
            !ret ==> *final(self) == *old(self),
            ret == old(self).can_derive_between(src, from, dst, to, rights, base, order, badge),
            ret ==> {
                let parent = old(self).tables.node_of(src, from);
                let child = old(self).tables.node_of(dst, to);
                &&& Self::cap_derived_between(*old(self), *final(self), src, from, dst, to, rights, base, order, badge)
                &&& Self::derive_step(*old(self), *final(self), child)
                &&& Self::derive_counted(*old(self), *final(self), parent)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent)
                &&& final(self).list.seq@[0] == old(self).list.seq@[0]
            },
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            final(self).threads.records == old(self).threads.records,
            final(self).threads.boot_thread == old(self).threads.boot_thread,
            final(self).threads.queues == old(self).threads.queues,
            final(self).endpoints.records == old(self).endpoints.records,
    {
        let ghost pre = *old(self);
        let (parent, payload) = match self.tables.lookup(&self.list, src, from) {
            Some(found) => found,
            None => { return false; },
        };
        let child = match self.tables.lookup(&self.list, dst, to) {
            Some(found) => found.0,
            None => { return false; },
        };
        let node = self.list.get(parent);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || node.depth >= MAX_DEPTH || self.list.get(child).live {
            return false;
        }
        proof {
            pre.lemma_slot(src, from);
            assert(pre.tables.is_cap(&pre.list, parent));
            assert(payload == pre.payload_of(parent));
            if payload.kind is Space {
                pre.lemma_space_cap(parent);
            }
            if payload.kind is Thread {
                pre.lemma_thread_cap(parent);
            }
            if payload.kind is Process {
                pre.lemma_process_cap(parent);
            }
            if payload.kind is Endpoint {
                pre.lemma_endpoint_cap(parent);
            }
        }
        if self.is_cap_dead(parent, payload) {
            return false;
        }
        // Only an endpoint's child takes a badge, and only from a parent that has none, so a badge is
        // fixed once set; it fits the 48 bits a receive returns it in.
        if badge != 0 {
            let endpoint = match payload.kind {
                CapKind::Endpoint => true,
                _ => false,
            };
            if !endpoint || payload.badge != 0 || badge >= BADGE_LIMIT {
                return false;
            }
        }
        // A device is bound to one space at a time, so its capability has no children: it moves instead.
        // A notification's or a reply's capability has none either: its retype makes the one capability that
        // names it. The console's, power's, an endpoint's and a core's name one page, so a child names that page
        // as its parent does. A core capability's child takes the order as its maximum priority, which it
        // may lower and not raise.
        let allowed = match payload.kind {
            CapKind::Device | CapKind::Notification | CapKind::Reply => false,
            CapKind::Console | CapKind::Power | CapKind::Endpoint => rights & !payload.rights == 0 && base == payload.base && order == payload.order,
            CapKind::Core => rights & !payload.rights == 0 && base == payload.base && order as usize <= payload.priority,
            _ => may_derive(payload, rights, base, order),
        };
        if !allowed {
            return false;
        }
        proof {
            if payload.kind is Console || payload.kind is Power || payload.kind is Endpoint {
                lemma_object_within(payload, base, order);
            }
            if payload.kind is Core {
                lemma_object_within(payload, base, 0);
            }
        }
        let (child_order, child_priority) = match payload.kind {
            CapKind::Core => (0u8, order as usize),
            _ => (order, 0usize),
        };
        let counted = match payload.kind {
            CapKind::Frame | CapKind::Space | CapKind::Thread | CapKind::Process | CapKind::Endpoint => true,
            _ => false,
        };
        // A derived frame, space, thread, process or endpoint holds a reference on the block its parent
        // lies in.
        let block = if counted {
            let br = locate(&self.blocks, payload.base / PAGE_SZ);
            if !add_block_ref(&mut self.blocks, br) {
                return false;
            }
            Some(br)
        } else {
            None
        };
        proof {
            self.list.lemma_seq_fits();
            self.list.lemma_valid_bound(parent);
            self.list.lemma_valid_bound(child);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
            // The new node is a slot, never the leaf's hidden node, so the slot is still found.
            pre.lemma_slot(dst, to);
            let leaf = pre.tables.leaf(dst, index_entry(to));
            pre.tables.lemma_leaf(&pre.list, leaf);
            lemma_slot_in_leaf(leaf, 0);
            pre.list.lemma_valid_bound(leaf);
            assert(self.list.nodes@[leaf as int].live == pre.list.nodes@[leaf as int].live);
        }
        self.tables.set_payload(
            &self.list,
            dst,
            to,
            Payload { kind: payload.kind, order: child_order, rights, base, badge: if badge == 0 { payload.badge } else { badge }, priority: child_priority },
        );
        match block {
            Some(br) => {
                match payload.kind {
                    CapKind::Space => {
                        self.spaces.holders = Ghost(pre.spaces.holders@.insert(base, pre.spaces.holders@[base].insert(child)));
                    },
                    CapKind::Thread => {
                        self.threads.holders = Ghost(pre.threads.holders@.insert(base, pre.threads.holders@[base].insert(child)));
                    },
                    CapKind::Process => {
                        self.processes.holders = Ghost(pre.processes.holders@.insert(base, pre.processes.holders@[base].insert(child)));
                    },
                    CapKind::Endpoint => {
                        self.endpoints.holders = Ghost(pre.endpoints.holders@.insert(base, pre.endpoints.holders@[base].insert(child)));
                    },
                    _ => { self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].insert(child))); },
                }
            },
            None => {},
        }
        proof {
            let post = *self;
            pre.lemma_slot(src, from);
            pre.lemma_slot(dst, to);
            assert(post.payload_of(child) == badged_child_of(payload, rights, base, order, badge));
            assert(cap_wf(post.payload_of(child)) == cap_wf(child_of(payload, rights, base, order)));
            assert(control_named(post.payload_of(child)) == control_named(child_of(payload, rights, base, order)));
            let parent_rights = payload.rights;
            assert(rights & !parent_rights == 0 && rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
            assert(control_named(pre.tables.payload_of(parent)));
            Self::lemma_derive_caps_wf(pre, post, child);
            Self::lemma_hidden_frame(pre, post, child, child);
            Self::lemma_table_nodes_caps_frame(pre, post, child, child);
            Self::lemma_space_nodes_caps_frame(pre, post, child, child);
            Self::lemma_bindings_caps_frame(pre, post, child, child);
            // The child keeps its parent's badge: badge_allowed sets one only below a parent with none.
            Self::lemma_caps_frame(pre, post, child, child, parent);
            assert(badge_kept_at(&post.list, &post.tables, child));
            Self::lemma_badges_caps_frame(pre, post, child, child);
            Self::lemma_derive_holders(pre, post, parent, child, block);
            Self::lemma_devices_caps_frame(pre, post, child, child);
            lemma_parents_derived(pre.list, post.list, parent, child);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_bound_threads_same(pre, post);
            assert(pre.view().holds(src, parent));
            assert(post.is_cap(child));
            assert(post.view().holds(dst, child));
        }
        true
    }

    /// The holders after a derive: a frame child joins its parent's block, a space's, thread's,
    /// process's or endpoint's child joins its parent's object, and any other child holds nothing. With them, what the blocks owe the rest of
    /// the invariant.
    proof fn lemma_derive_holders(pre: Self, post: Self, parent: usize, child: usize, block: Option<BlockRef>)
        requires
            Self::derive_step(pre, post, child),
            pre.is_cap(parent),
            post.is_cap(child),
            narrows(post.payload_of(child), pre.payload_of(parent)),
            post.payload_of(child).kind == pre.payload_of(parent).kind,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            block is Some == tracked_kind(pre.payload_of(parent).kind),
            block is Some ==> {
                let br = block->0;
                &&& br == block_ref(&pre.blocks, pre.payload_of(parent).base / PAGE_SZ)
                &&& block_refs(&pre.blocks, br) < usize::MAX
                &&& blocks_refs_changed(&pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br))
            },
            block is Some && pre.payload_of(parent).kind is Frame ==> {
                &&& post.holders@ == pre.holders@.insert(block->0, pre.holders@[block->0].insert(child))
                &&& post.spaces == pre.spaces
                &&& post.threads == pre.threads
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Space ==> {
                let s = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces.roots == pre.spaces.roots
                &&& post.spaces.records == pre.spaces.records
                &&& post.spaces.loaded == pre.spaces.loaded
                &&& post.spaces.kernel_entries == pre.spaces.kernel_entries
                &&& post.spaces.registers == pre.spaces.registers
                &&& post.spaces.kernel_root == pre.spaces.kernel_root
                &&& post.spaces.bound == pre.spaces.bound
                &&& post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].insert(child))
                &&& post.threads == pre.threads
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Thread ==> {
                let t = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces == pre.spaces
                &&& post.threads.records == pre.threads.records
                &&& post.threads.boot_thread == pre.threads.boot_thread
                &&& post.threads.queues == pre.threads.queues
                &&& post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].insert(child))
                &&& post.processes == pre.processes
            },
            block is Some && pre.payload_of(parent).kind is Process ==> {
                let p = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces == pre.spaces
                &&& post.threads == pre.threads
                &&& post.processes.records == pre.processes.records
                &&& post.processes.spare == pre.processes.spare
                &&& post.processes.bound == pre.processes.bound
                &&& post.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].insert(child))
            },
            block is Some && pre.payload_of(parent).kind is Endpoint ==> {
                let e = pre.payload_of(parent).base;
                &&& post.holders == pre.holders
                &&& post.spaces == pre.spaces
                &&& post.threads == pre.threads
                &&& post.processes == pre.processes
                &&& post.endpoints.records == pre.endpoints.records
                &&& post.endpoints.holders@ == pre.endpoints.holders@.insert(e, pre.endpoints.holders@[e].insert(child))
            },
            block is None ==> post.blocks == pre.blocks && post.holders == pre.holders && post.spaces == pre.spaces
                && post.threads == pre.threads && post.processes == pre.processes,
            !(pre.payload_of(parent).kind is Notification),
            !(pre.payload_of(parent).kind is Reply),
            !(pre.payload_of(parent).kind is Endpoint) ==> post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            post.table_pages == pre.table_pages,
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        pre.lemma_slot_not_owned(child);
        Self::lemma_same_leaf_nodes(pre, post, child, child);
        pre.lemma_slot_not_table_page(child);
        Self::lemma_same_table_nodes(pre, post, child, child);
        let pp = pre.payload_of(parent);
        let cp = post.payload_of(child);
        match block {
            Some(br) => {
                if pp.kind is Frame {
                    lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, parent);
                    assert(frame_in_block(block_ref(&pre.blocks, pp.base / PAGE_SZ), pp));
                    lemma_child_same_block(&pre.blocks, pp, cp);
                    lemma_holders_frame_added(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, child, br);
                    lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_refs_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, post.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_refs_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    if let BlockRef::Small(x) = br {
                        assert(pre.blocks.pages@[x as int].object is Frame);
                    }
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_endpoints_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_replies_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else if pp.kind is Space {
                    // A space is its block's base, so the child names the parent's space.
                    pre.lemma_space_cap(parent);
                    let s = pp.base;
                    assert(br == BlockRef::Small(s / PAGE_SZ));
                    assert(cp.base == s);
                    assert(cp.order == 3);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(s / PAGE_SZ) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_spaces_holder_added(pre, post, child, s);
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_endpoints_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_replies_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else if pp.kind is Thread {
                    // A thread is its block's base, so the child names the parent's thread.
                    pre.lemma_thread_cap(parent);
                    let t = pp.base;
                    assert(br == BlockRef::Small(t / PAGE_SZ));
                    assert(cp.base == t);
                    assert(cp.order == THREAD_ORDER);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(t / PAGE_SZ) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, t / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, t / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, t / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, t / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_threads_holder_added(pre, post, child, t);
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_endpoints_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_replies_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else if pp.kind is Process {
                    // A process is its block's base, so the child names the parent's process.
                    pre.lemma_process_cap(parent);
                    let p = pp.base;
                    assert(br == BlockRef::Small(p / PAGE_SZ));
                    assert(cp.base == p);
                    assert(cp.order == PROCESS_ORDER);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(p / PAGE_SZ) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_processes_holder_added(pre, post, child, p);
                    lemma_endpoints_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_replies_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                } else {
                    // An endpoint is its block's base, so the child names the parent's endpoint.
                    pre.lemma_endpoint_cap(parent);
                    let e = pp.base;
                    assert(br == BlockRef::Small(e / PAGE_SZ));
                    assert(cp.base == e);
                    assert(cp.order == 0);
                    lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                    assert(!pre.holders@.contains_key(br)) by {
                        if pre.holders@.contains_key(br) {
                            assert(pre.blocks.pages@[(e / PAGE_SZ) as int].object is Frame);
                        }
                    }
                    lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, e / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, e / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
                    assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
                    lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, e / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                    lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, e / PAGE_SZ, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    lemma_replies_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, br, (block_refs(&pre.blocks, br) + 1) as usize, block_dead(&pre.blocks, br));
                    Self::lemma_endpoints_holder_added(pre, post, child, e);
                }
            },
            None => {
                lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
                assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
                lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
                lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
                lemma_spaces_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks);
                lemma_threads_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks);
                lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
                lemma_endpoints_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks);
                lemma_replies_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks);
            },
        }
    }

    /// What a derive does to the fields the view reads.
    pub open spec fn derive_step(pre: Self, post: Self, child: usize) -> bool {
        &&& Self::caps_frame(pre, post, child, child)
        &&& !pre.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].kind is Capability
    }

    /// Every capability still names a block.
    pub proof fn lemma_derive_caps_wf(pre: Self, post: Self, child: usize)
        requires
            Self::derive_step(pre, post, child),
            cap_wf(post.payload_of(child)),
            control_named(post.payload_of(child)),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
    {
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies {
            &&& cap_wf(post.tables.payload_of(n))
            &&& control_named(post.tables.payload_of(n))
        } by {
            if n != child {
                Self::lemma_caps_frame(pre, post, child, child, n);
                assert(post.is_cap(n));
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
    }

    /// What a step that makes one capability, in a slot, does to the others: nothing. A derive is one,
    /// and so is a retype that adds node pages, which keeps every node the list held but says nothing
    /// of the kinds in the pages it adds.
    pub open spec fn adds_cap(pre: Self, post: Self, child: usize) -> bool {
        &&& pre.wf()
        &&& post.tables.owner == pre.tables.owner
        &&& forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
            x != child ==> post.is_cap(x) == pre.is_cap(x)
        &&& forall|x: usize| x != child && #[trigger] pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x)
        &&& !pre.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].live
        &&& post.list.nodes@[child as int].kind is Capability
    }

    pub proof fn lemma_derive_step_adds_cap(pre: Self, post: Self, child: usize)
        requires
            Self::derive_step(pre, post, child),
        ensures
            Self::adds_cap(pre, post, child),
    {
        assert forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
            x != child implies post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
        assert forall|x: usize| x != child && #[trigger] pre.is_cap(x) implies post.payload_of(x) == pre.payload_of(x) by {
            Self::lemma_caps_frame(pre, post, child, child, x);
        }
    }

    /// A capability is listed below its parent, a live node: it is in a slot, and the list's first node
    /// is in none.
    pub proof fn lemma_parent_of_cap(&self, x: usize)
        requires
            self.wf(),
            self.is_cap(x),
        ensures
            x < NODE_SPACE,
            self.list.parent@.contains_key(x),
            self.list.parent@[x] < NODE_SPACE,
            self.list.nodes@[self.list.parent@[x] as int].live,
            self.list.is_child(self.list.parent@[x], x),
            self.list.parent@[x] != x,
    {
        self.lemma_slot_bound(x);
        let s = self.list.seq@;
        assert(has(s, x));
        lemma_has(s, x);
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        assert(x != s[0]);
        assert(k != 0);
        assert(self.list.parent@.contains_key(s[k]));
        assert(self.list.d(s[k]) == self.list.d(self.list.parent@[s[k]]) + 1);
        self.list.lemma_parent_live(x);
    }

    /// A capability below a capability keeps its badge.
    pub proof fn lemma_badge_inherited(&self, x: usize)
        requires
            self.wf(),
            self.is_cap(x),
        ensures
            badge_kept_at(&self.list, &self.tables, x),
    {
        reveal(badges_inherited);
        assert(self.tables.is_cap(&self.list, x));
    }

    /// The badges after a step that changed no node but n and m and renamed n to m in the parent map
    /// at most. A capability below n is below m after, which says what n did, unless n was childless;
    /// n and m are capabilities after only if they were or were not live, and each keeps its parent's
    /// badge; and a step that renames renames a capability.
    pub proof fn lemma_badges_caps_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            forall|x: usize| x != n && x != m && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == rename(pre.list.parent@[x], n, m),
            pre.is_cap(n) ==> pre.list.childless(n) || (post.is_cap(m) && post.payload_of(m) == pre.payload_of(n)),
            pre.is_cap(m) && m != n ==> pre.list.childless(m),
            n != m ==> pre.is_cap(n),
            post.is_cap(n) ==> pre.is_cap(n) || !pre.list.nodes@[n as int].live,
            post.is_cap(m) ==> pre.is_cap(m) || !pre.list.nodes@[m as int].live,
            post.is_cap(n) ==> badge_kept_at(&post.list, &post.tables, n),
            post.is_cap(m) ==> badge_kept_at(&post.list, &post.tables, m),
        ensures
            badges_inherited(&post.list, &post.tables),
    {
        reveal(badges_inherited);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x)
            implies badge_kept_at(&post.list, &post.tables, x) by {
            assert(post.is_cap(x));
            if x != n && x != m {
                Self::lemma_caps_frame(pre, post, n, m, x);
                pre.lemma_parent_of_cap(x);
                let a = pre.list.parent@[x];
                assert(pre.tables.is_cap(&pre.list, x));
                assert(badge_kept_at(&pre.list, &pre.tables, x));
                assert(post.list.parent@[x] == rename(a, n, m));
                if a == n {
                    if pre.is_cap(n) && pre.list.childless(n) {
                        pre.list.lemma_childless(n, x);
                    }
                } else if a == m {
                    if pre.is_cap(m) {
                        pre.list.lemma_childless(m, x);
                    }
                } else {
                    Self::lemma_caps_frame(pre, post, n, m, a);
                }
            }
        }
    }

    /// The badges after a step that kept every capability's parent and what it says, and added none
    /// but in nodes that were not live, each keeping its parent's badge.
    pub proof fn lemma_badges_kept(pre: Self, post: Self)
        requires
            pre.wf(),
            forall|x: usize| #[trigger] post.is_cap(x) ==> (pre.is_cap(x) && post.payload_of(x) == pre.payload_of(x))
                || (!pre.list.nodes@[x as int].live && badge_kept_at(&post.list, &post.tables, x)),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.list.parent@[x] == pre.list.parent@[x],
        ensures
            badges_inherited(&post.list, &post.tables),
    {
        reveal(badges_inherited);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x)
            implies badge_kept_at(&post.list, &post.tables, x) by {
            assert(post.is_cap(x));
            if pre.is_cap(x) && post.payload_of(x) == pre.payload_of(x) {
                pre.lemma_parent_of_cap(x);
                let a = pre.list.parent@[x];
                assert(post.list.parent@[x] == a);
                assert(pre.tables.is_cap(&pre.list, x));
                assert(badge_kept_at(&pre.list, &pre.tables, x));
                if post.is_cap(a) {
                    assert(pre.is_cap(a) && post.payload_of(a) == pre.payload_of(a));
                }
            }
        }
    }

    /// The badges after a step that kept every capability, what it says and the parent map.
    pub proof fn lemma_badges_same_caps(pre: Self, post: Self)
        requires
            pre.wf(),
            forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            post.list.parent == pre.list.parent,
        ensures
            badges_inherited(&post.list, &post.tables),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            assert(post.tables.is_cap(&post.list, x));
        }
        Self::lemma_badges_kept(pre, post);
    }

    /// The badges after a step that adds one node that is no capability and changes no capability.
    pub proof fn lemma_badges_node_added(pre: Self, post: Self, n: usize, c: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            !pre.list.nodes@[n as int].live,
            !(post.list.nodes@[n as int].kind is Capability),
            post.list.parent@ == pre.list.parent@.insert(n, c),
        ensures
            badges_inherited(&post.list, &post.tables),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
            if x != n {
                Self::lemma_caps_frame(pre, post, n, n, x);
            }
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.list.parent@[x] == pre.list.parent@[x] by {
            assert(x != n);
        }
        Self::lemma_badges_kept(pre, post);
    }

    /// The badges after a step that derives one child: it keeps its parent's badge, or its parent is
    /// the list's first node, which is no capability; every other capability is as it was.
    pub proof fn lemma_badges_derived(pre: Self, post: Self, parent: usize, child: usize)
        requires
            Self::caps_frame(pre, post, child, child),
            forall|x: usize| x != child && x != child && #[trigger] pre.list.parent@.contains_key(x)
                ==> post.list.parent@.contains_key(x) && post.list.parent@[x] == rename(pre.list.parent@[x], child, child),
            !pre.list.nodes@[child as int].live,
            parent != child,
            post.list.parent@.contains_key(child),
            post.list.parent@[child] == parent,
            parent == pre.list.seq@[0] || badge_kept(pre.payload_of(parent), post.payload_of(child)),
        ensures
            badges_inherited(&post.list, &post.tables),
    {
        Self::lemma_caps_frame(pre, post, child, child, parent);
        if parent == pre.list.seq@[0] {
            assert(first_node_outside_leaves(&pre.list, &pre.tables));
            assert(!pre.is_cap(parent));
        }
        assert(badge_kept_at(&post.list, &post.tables, child));
        Self::lemma_badges_caps_frame(pre, post, child, child);
    }

    /// The view of a step that adds one child, in a slot of the table at dst, under a capability held
    /// in the table at src, covering only what its parent does.
    #[verifier::spinoff_prover]
    pub proof fn lemma_places_node_view(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize)
        requires
            post.frames@ == pre.frames@,
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            Self::adds_cap(pre, post, pre.tables.node_of(dst, to)),
            post.view().shares == pre.view().shares,
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, src, from),
            pre.tables.has_slot(&pre.list, dst, to),
            pre.is_cap(pre.tables.node_of(src, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(dst, to), pre.tables.node_of(src, from)),
            ({
                let cp = post.payload_of(pre.tables.node_of(dst, to));
                let pp = pre.payload_of(pre.tables.node_of(src, from));
                block_within(cp.base, cp.order, pp)
            }),
        ensures
            post.view().holds(dst, pre.tables.node_of(dst, to)),
            places_node(
                pre.view(),
                post.view(),
                src,
                dst,
                pre.tables.node_of(src, from),
                pre.tables.node_of(dst, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
            ),
    {
        // The proof reads the list's part of wf alone; the rest stays folded, out of the solver's search.
        hide(CapKernel::wf);
        assert(pre.list.wf()) by {
            reveal(CapKernel::wf);
        }
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        pre.lemma_slot(src, from);
        pre.lemma_slot(dst, to);
        assert(a.holds(src, parent));
        assert(b.holds(dst, child));
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) by {
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies live(x) by {
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies live(a.parent[x]) by {
            pre.list.lemma_parent_live(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) == (a.held.contains(h) || h == (dst, child)) by {
            if h.1 != child {
                assert(post.is_cap(h.1) == pre.is_cap(h.1));
            }
        }
        assert forall|x: NodeId| x != child implies {
            &&& #[trigger] b.names.contains_key(x) == a.names.contains_key(x)
            &&& b.pages.contains_key(x) == a.pages.contains_key(x)
            &&& a.names.contains_key(x) ==> b.names[x] == a.names[x]
            &&& a.pages.contains_key(x) ==> b.pages[x] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| x != child implies #[trigger] b.rights.contains((x, r)) == a.rights.contains((x, r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        assert forall|o: ObjectId| #[trigger] b.covers(child, o) implies a.covers(parent, o) by {
            assert(block_bytes(cp.order) == b.pages[child] * PAGE_SZ);
            assert(block_bytes(pp.order) == a.pages[parent] * PAGE_SZ);
        }
        assert forall|o: ObjectId| #[trigger] (b.contents)(o) == (a.contents)(o) by {}
        pre.lemma_slot_bound(parent);
        pre.lemma_slot_bound(child);
        assert(live(parent));
        assert(!live(child));
        assert(b.parent == a.parent.insert(child, parent));
        assert(b.maps == a.maps);
        assert(places_node(a, b, src, dst, parent, child, live));
    }

    /// And has control only with its parent's name.
    pub proof fn lemma_places_child_view(pre: Self, post: Self, src: usize, from: usize, dst: usize, to: usize)
        requires
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            post.frames@ == pre.frames@,
            Self::adds_cap(pre, post, pre.tables.node_of(dst, to)),
            post.view().shares == pre.view().shares,
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, src, from),
            pre.tables.has_slot(&pre.list, dst, to),
            pre.is_cap(pre.tables.node_of(src, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(dst, to), pre.tables.node_of(src, from)),
            ({
                let cp = post.payload_of(pre.tables.node_of(dst, to));
                let pp = pre.payload_of(pre.tables.node_of(src, from));
                &&& block_within(cp.base, cp.order, pp)
                &&& cp.rights & right_bit(Right::Control) != 0 ==> {
                    &&& pp.rights & right_bit(Right::Control) != 0
                    &&& cp.base == pp.base
                }
            }),
        ensures
            post.view().holds(dst, pre.tables.node_of(dst, to)),
            places_child(
                pre.view(),
                post.view(),
                src,
                dst,
                pre.tables.node_of(src, from),
                pre.tables.node_of(dst, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
            ),
    {
        let parent = pre.tables.node_of(src, from);
        let child = pre.tables.node_of(dst, to);
        Self::lemma_places_node_view(pre, post, src, from, dst, to);
        pre.lemma_slot(src, from);
        pre.lemma_slot(dst, to);
    }

    /// What derive's child owes that view: control only with the parent's name, and all its other
    /// rights the parent's too.
    proof fn lemma_derive_discharges(pre: Self, post: Self, root: usize, from: usize, to: usize)
        requires
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            post.frames@ == pre.frames@,
            Self::derive_step(pre, post, pre.tables.node_of(root, to)),
            Self::same_tree(pre, post),
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            narrows(post.payload_of(pre.tables.node_of(root, to)), pre.payload_of(pre.tables.node_of(root, from))),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        let (child_rights, parent_rights) = (cp.rights, pp.rights);
        assert(child_rights & !parent_rights == 0 && child_rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
        assert(right_bit(Right::Control) == 128);
        Self::lemma_derive_step_adds_cap(pre, post, child);
        Self::lemma_places_child_view(pre, post, root, from, root, to);
        let (a, b) = (pre.view(), post.view());
        assert(a.names.contains_key(parent));
        assert forall|r: Right| #[trigger] b.rights.contains((child, r)) implies a.rights.contains((parent, r)) by {
            let bit = right_bit(r);
            assert(child_rights & !parent_rights == 0 && child_rights & bit != 0 ==> parent_rights & bit != 0) by (bit_vector);
        }
        lemma_adds_child_discharges(a, b, root, parent, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live);
    }

    /// The view of a derive into a controlled process's table: the caller, holding control over the
    /// process at d through capability c, put a child of the capability at its own index from in the
    /// slot at index to of that process's table. Reach grows only for that process and what controls
    /// it, by what the caller reached.
    proof fn lemma_derive_into_discharges(pre: Self, post: Self, root: usize, c: usize, from: usize, d: usize, to: usize)
        requires
            saved_registers(&post.threads) == saved_registers(&pre.threads),
            post.frames@ == pre.frames@,
            Self::derive_step(pre, post, pre.tables.node_of(d, to)),
            Self::same_tree(pre, post),
            post.devices == pre.devices,
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, d, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(d, to), pre.tables.node_of(root, from)),
            narrows(post.payload_of(pre.tables.node_of(d, to)), pre.payload_of(pre.tables.node_of(root, from))),
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            pre.payload_of(c).rights & right_bit(Right::Control) != 0,
            pre.payload_of(c).base == d,
        ensures
            discharges(pre.view(), post.view(), root, Effect::Place { cap: c, from: pre.tables.node_of(root, from) }),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(d, to);
        let (cp, pp) = (post.payload_of(child), pre.payload_of(parent));
        let (child_rights, parent_rights) = (cp.rights, pp.rights);
        assert(child_rights & !parent_rights == 0 && child_rights & 128 != 0 ==> parent_rights & 128 != 0) by (bit_vector);
        assert(right_bit(Right::Control) == 128);
        Self::lemma_derive_step_adds_cap(pre, post, child);
        Self::lemma_places_child_view(pre, post, root, from, d, to);
        let a = pre.view();
        assert(a.holds_right(root, c, Right::Control));
        assert(a.names[c] == d);
        assert(!a.process_of.contains_key(d));
        assert(a.names.contains_key(parent));
        assert forall|r: Right| #[trigger] post.view().rights.contains((child, r)) implies a.rights.contains((parent, r)) by {
            let bit = right_bit(r);
            assert(child_rights & !parent_rights == 0 && child_rights & bit != 0 ==> parent_rights & bit != 0) by (bit_vector);
        }
        lemma_places_child_discharges(a, post.view(), root, d, c, parent, child, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live);
    }
}

} // verus!
