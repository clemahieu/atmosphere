//! Moving a capability within its table, and claiming one from the table of a process the caller
//! controls. The node keeps its place and depth, so every child comes along. A capability's identity in
//! the view is its node id, which a move renames, so reach is carried across by that renaming: in both
//! directions within one table, and for a claim back from the caller to the process it took from, which
//! it controls. See design/sharing-by-derive/.
use vstd::prelude::*;

verus! {

use crate::capability::device::*;
use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::process::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;

impl CapKernel {
    /// The refusals: an index that names no slot, a source with no capability, or a target in use,
    /// which a source is, so a slot cannot move onto itself.
    pub open spec fn can_move_between(&self, src: usize, from: usize, dst: usize, to: usize) -> bool {
        &&& self.tables.has_slot(&self.list, src, from)
        &&& self.tables.has_slot(&self.list, dst, to)
        &&& self.is_cap(self.tables.node_of(src, from))
        &&& !self.list.nodes@[self.tables.node_of(dst, to) as int].live
    }

    /// A move's refusals, beyond those within a table: a source naming a dead process or thread.
    pub open spec fn can_move(&self, root: usize, from: usize, to: usize) -> bool {
        &&& self.can_move_between(root, from, root, to)
        &&& !self.cap_dead(self.tables.node_of(root, from))
    }

    /// A claim's refusals, beyond a move's: the index `cap` names no capability, or one that is not a
    /// process's or lacks control. Whether the process is dead is not read.
    pub open spec fn can_claim(&self, root: usize, cap: usize, from: usize, to: usize) -> bool {
        let c = self.tables.node_of(root, cap);
        &&& self.tables.has_slot(&self.list, root, cap)
        &&& self.is_cap(c)
        &&& self.payload_of(c).kind is Process
        &&& self.payload_of(c).rights & right_bit(Right::Control) != 0
        &&& self.can_move_between(self.payload_of(c).base, from, root, to)
    }

    /// What a move of the capability at index from of the table at root to index to did: the move was
    /// allowed, the node took the empty node's place in the list at the same depth under the same parent
    /// with the same payload, every child came along, the source holds no capability and the destination
    /// is held, reach is unchanged, and the step discharges a local effect.
    pub open spec fn cap_moved(pre: Self, post: Self, root: usize, from: usize, to: usize) -> bool {
        let i = pre.tables.node_of(root, from);
        let n = pre.tables.node_of(root, to);
        &&& pre.can_move(root, from, to)
        &&& exists|p: int| 0 <= p < pre.list.seq@.len() && #[trigger] pre.list.seq@[p] == i
            && post.list.seq@ == pre.list.seq@.update(p, n)
        &&& post.list.nodes@[n as int].depth == pre.list.nodes@[i as int].depth
        &&& post.list.parent@ == moved_parent(pre.list.parent@, i, n)
        &&& post.payload_of(n) == pre.payload_of(i)
        &&& !post.is_cap(i)
        &&& post.view().holds(root, n)
        &&& Self::caps_frame(pre, post, i, n)
        &&& forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o)
        &&& discharges(pre.view(), post.view(), root, Effect::Local)
    }

    /// Moves the capability at index `from` of the table at `root` to the empty index `to`. The indices
    /// come from user space, so either can be refused, and a refusal changes nothing.
    pub fn move_cap(&mut self, root: usize, from: usize, to: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::same_tree(*old(self), *final(self)),
            ret == old(self).can_move(root, from, to),
            !ret ==> *final(self) == *old(self),
            ret ==> Self::cap_moved(*old(self), *final(self), root, from, to),
            discharges(old(self).view(), final(self).view(), root, Effect::Local),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_op_discharges(root);
        }
        if let Some((i, payload)) = self.tables.lookup(&self.list, root, from) {
            let node = self.list.get(i);
            let kind_ok = match node.kind {
                NodeKind::Capability => true,
                _ => false,
            };
            if node.live && kind_ok {
                proof {
                    pre.lemma_slot(root, from);
                    assert(pre.tables.is_cap(&pre.list, i));
                    assert(payload == pre.payload_of(i));
                }
                if self.is_cap_dead(i, payload) {
                    return false;
                }
            }
        }
        let ret = self.move_between(root, from, root, to);
        if ret {
            proof {
                let i = pre.tables.node_of(root, from);
                let n = pre.tables.node_of(root, to);
                Self::lemma_move_discharges(pre, *self, root, i, n);
            }
        }
        ret
    }

    /// Moves the capability at index `from` of the table of the process that the capability at index
    /// `cap` of the table at `root` names, to the empty index `to` at `root`. That capability must be a
    /// process's, not a thread's, and carry control; the process may be live or dead. One bounded step:
    /// nothing enumerates the process's table. The indices come from user space, so any can be refused,
    /// and a refusal changes nothing.
    pub fn claim(&mut self, root: usize, cap: usize, from: usize, to: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            Self::same_tree(*old(self), *final(self)),
            ret == old(self).can_claim(root, cap, from, to),
            !ret ==> *final(self) == *old(self),
            !(old(self).payload_of(old(self).tables.node_of(root, cap)).kind is Process) ==> !ret,
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret ==> {
                let c = old(self).tables.node_of(root, cap);
                let i = old(self).tables.node_of(old(self).payload_of(c).base, from);
                let n = old(self).tables.node_of(root, to);
                &&& exists|p: int| 0 <= p < old(self).list.seq@.len() && #[trigger] old(self).list.seq@[p] == i
                    && final(self).list.seq@ == old(self).list.seq@.update(p, n)
                &&& final(self).list.nodes@[n as int].depth == old(self).list.nodes@[i as int].depth
                &&& final(self).list.parent@ == moved_parent(old(self).list.parent@, i, n)
                &&& final(self).payload_of(n) == old(self).payload_of(i)
                &&& !final(self).is_cap(i)
                &&& final(self).view().holds(root, n)
                &&& Self::caps_frame(*old(self), *final(self), i, n)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Claim { cap: c, from: i })
            },
    {
        let ghost pre = *old(self);
        let (c, payload) = match self.tables.lookup(&self.list, root, cap) {
            Some(found) => found,
            None => { return false; },
        };
        let node = self.list.get(c);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok {
            return false;
        }
        let process_ok = match payload.kind {
            CapKind::Process => true,
            _ => false,
        };
        proof {
            pre.lemma_slot(root, cap);
            assert(pre.tables.is_cap(&pre.list, c));
            assert(payload == pre.payload_of(c));
            assert(right_bit(Right::Control) == 128);
        }
        if !process_ok || payload.rights & 128 == 0 {
            return false;
        }
        let q = payload.base;
        proof {
            assert(pre.processes.records@.contains_key(q));
            assert(pre.tables.roots@.contains_key(q));
        }
        let ret = self.move_between(q, from, root, to);
        if ret {
            proof {
                let i = pre.tables.node_of(q, from);
                let n = pre.tables.node_of(root, to);
                Self::lemma_claim_discharges(pre, *self, root, c, i, n);
            }
        }
        ret
    }

    /// Moves the capability at index `from` of the table at `src` to the empty index `to` of the table at
    /// `dst`: a move when they are one table, a claim's step when not. A refusal changes nothing.
    fn move_between(&mut self, src: usize, from: usize, dst: usize, to: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(src),
            old(self).tables.roots@.contains_key(dst),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::same_tree(*old(self), *final(self)),
            ret == old(self).can_move_between(src, from, dst, to),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let i = old(self).tables.node_of(src, from);
                let n = old(self).tables.node_of(dst, to);
                &&& exists|p: int| 0 <= p < old(self).list.seq@.len() && #[trigger] old(self).list.seq@[p] == i
                    && final(self).list.seq@ == old(self).list.seq@.update(p, n)
                &&& final(self).list.nodes@[n as int].depth == old(self).list.nodes@[i as int].depth
                &&& final(self).list.parent@ == moved_parent(old(self).list.parent@, i, n)
                &&& final(self).payload_of(n) == old(self).payload_of(i)
                &&& !final(self).is_cap(i)
                &&& final(self).view().holds(dst, n)
                &&& Self::caps_frame(*old(self), *final(self), i, n)
                &&& Self::move_step(*old(self), *final(self), i, n)
                &&& old(self).tables.owner@[page_of(i)].0 == src
                &&& old(self).tables.owner@[page_of(n)].0 == dst
            },
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
    {
        let ghost pre = *old(self);
        let (i, payload) = match self.tables.lookup(&self.list, src, from) {
            Some(found) => found,
            None => { return false; },
        };
        let n = match self.tables.lookup(&self.list, dst, to) {
            Some(found) => found.0,
            None => { return false; },
        };
        let node = self.list.get(i);
        let kind_ok = match node.kind {
            NodeKind::Capability => true,
            _ => false,
        };
        if !node.live || !kind_ok || self.list.get(n).live {
            return false;
        }
        proof {
            pre.lemma_slot(src, from);
            pre.lemma_slot(dst, to);
            assert(pre.tables.is_cap(&pre.list, i));
            assert(payload == pre.payload_of(i));
            self.list.lemma_valid_bound(i);
            self.list.lemma_valid_bound(n);
        }
        self.list.move_node(i, n);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(&self.list, dst, to, payload);
        // A frame's holder has a new name; the count does not change.
        self.holders = Ghost(Self::moved_holders(pre.holders@, i, n));
        self.spaces.holders = Ghost(moved_space_holders(pre.spaces.holders@, i, n));
        self.threads.holders = Ghost(moved_thread_holders(pre.threads.holders@, i, n));
        self.processes.holders = Ghost(moved_process_holders(pre.processes.holders@, i, n));
        // A device's one capability has a new name.
        if let CapKind::Device = payload.kind {
            self.devices.holder = Ghost(pre.devices.holder@.insert(payload.base, n));
        }
        proof {
            let post = *self;
            assert(post.list.nodes@[n as int].kind == pre.list.nodes@[i as int].kind);
            assert(post.payload_of(n) == pre.payload_of(i));
            assert(Self::caps_frame(pre, post, i, n));
            Self::lemma_move_caps_wf(pre, post, i, n);
            Self::lemma_hidden_frame(pre, post, i, n);
            Self::lemma_table_nodes_caps_frame(pre, post, i, n);
            Self::lemma_space_nodes_caps_frame(pre, post, i, n);
            assert(post.is_cap(n));
            Self::lemma_bindings_caps_frame(pre, post, i, n);
            Self::lemma_move_holders(pre, post, i, n);
            Self::lemma_move_mappings(pre, post, i, n);
            Self::lemma_move_devices(pre, post, i, n);
            lemma_parents_moved(pre.list, post.list, i, n);
            Self::lemma_tlb_same(pre, post);
            assert(post.view().holds(dst, n));
            Self::lemma_bound_threads_same(pre, post);
        }
        true
    }

    /// The holders after a move: the node a frame held its block by has a new name, and no count changed.
    proof fn lemma_move_holders(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            post.blocks == pre.blocks,
            post.zeroing == pre.zeroing,
            post.holders@ == Self::moved_holders(pre.holders@, i, n),
            post.table_pages == pre.table_pages,
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.mappings == pre.mappings,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let ha = pre.holders@;
        let hb = post.holders@;
        let blocks = &pre.blocks;
        assert(pre.tables.is_cap(&pre.list, i));
        assert(same_mapping_nodes(&pre.list, &post.list));
        pre.lemma_slot_not_owned(i);
        pre.lemma_slot_not_owned(n);
        Self::lemma_same_leaf_nodes(pre, post, i, n);
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, &post.blocks);
        pre.lemma_slot_not_table_page(i);
        pre.lemma_slot_not_table_page(n);
        Self::lemma_same_table_nodes(pre, post, i, n);
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, &post.blocks);
        assert(!pre.tables.is_cap(&pre.list, n));
        assert(!post.tables.is_cap(&post.list, i));
        assert forall|x: usize| x != i && x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, i, n, x);
        }
        assert forall|k: BlockRef| #[trigger] hb.contains_key(k) == ha.contains_key(k) by {}
        assert forall|k: BlockRef| ha.contains_key(k) implies {
            &&& #[trigger] hb[k] == (if ha[k].contains(i) { ha[k].remove(i).insert(n) } else { ha[k] })
            &&& !ha[k].contains(n)
        } by {
            if ha[k].contains(n) {
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Frame implies {
            let p = post.tables.payload_of(x).base / 4096;
            &&& blocks.tracks(p as int)
            &&& frame_in_block(block_ref(blocks, p), post.tables.payload_of(x))
            &&& hb.contains_key(block_ref(blocks, p))
            &&& hb[block_ref(blocks, p)].contains(x)
        } by {
            let p = post.tables.payload_of(x).base / 4096;
            if x == n {
                assert(ha[block_ref(blocks, p)].contains(i));
            } else {
                assert(pre.tables.is_cap(&pre.list, x));
                assert(ha[block_ref(blocks, p)].contains(x));
            }
        }
        assert forall|k: BlockRef| #[trigger] hb.contains_key(k) implies {
            &&& hb[k].finite()
            &&& hb[k].len() == block_refs(blocks, k)
            &&& block_typed(blocks, k)
            &&& block_refs(blocks, k) == 0 ==> block_dead(blocks, k)
            &&& !block_active(&post.zeroing, k)
        } by {
            assert(ha.contains_key(k));
            if ha[k].contains(i) {
                vstd::set::lemma_set_remove_len(ha[k], i);
                vstd::set::lemma_set_insert_len(ha[k].remove(i), n);
            }
        }
        assert forall|k: BlockRef, x: usize| hb.contains_key(k) && #[trigger] hb[k].contains(x) implies ({
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Frame
            &&& blocks.tracks_addr(post.tables.payload_of(x).base)
            &&& block_ref(blocks, post.tables.payload_of(x).base / 4096) == k
        } || (x < NODE_SPACE && post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is Mapping)) by {
            assert(ha.contains_key(k));
            if ha[k].contains(i) && x == n {
                assert(ha[k].contains(i));
            } else {
                assert(ha[k].contains(x));
                assert(x != i);
                assert(x != n);
                if pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Frame {
                    assert(post.tables.is_cap(&post.list, x));
                } else {
                    assert(x < NODE_SPACE && pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Mapping);
                    assert(post.list.nodes@[x as int].live && post.list.nodes@[x as int].kind is Mapping);
                }
            }
        }
    }

    /// The mappings after a move: a mapping whose parent was i has n, which says the same, and every
    /// other mapping's parent is as it was. No mapping node, frame block or holder changed.
    proof fn lemma_move_mappings(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            post.blocks == pre.blocks,
            post.holders@ == Self::moved_holders(pre.holders@, i, n),
            post.table_pages == pre.table_pages,
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.mappings == pre.mappings,
            post.list.pages@.dom() == pre.list.pages@.dom(),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert(Self::same_tree(pre, post));
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            let c = pre.list.parent@[m];
            assert(m != i);
            assert(m != n);
            assert(post.list.parent@.contains_key(m));
            assert(post.list.parent@[m] == rename(c, i, n));
            if c == i {
                assert(post.is_cap(n));
            } else {
                assert(c != n);
                Self::lemma_caps_frame(pre, post, i, n, c);
            }
            let br = block_ref(&pre.blocks, pre.mappings@[m].frame);
            assert(post.holders@[br] == (if pre.holders@[br].contains(i) { pre.holders@[br].remove(i).insert(n) } else { pre.holders@[br] }));
        }
        Self::lemma_mappings_same_tree(pre, post);
    }

    /// The devices after a move: a device whose capability was i has n, which says the same, and a
    /// device capability other than i names another device, so its entry is as it was.
    proof fn lemma_move_devices(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            post.devices.records == pre.devices.records,
            post.devices.count == pre.devices.count,
            post.devices.holder@ == if pre.payload_of(i).kind is Device {
                pre.devices.holder@.insert(pre.payload_of(i).base, n)
            } else {
                pre.devices.holder@
            },
        ensures
            devices_wf(&post.list, &post.tables, &post.devices),
    {
        reveal(devices_wf);
        let (pp, base) = (pre.payload_of(i), pre.payload_of(i).base);
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Device implies {
            &&& post.tables.payload_of(x).order == 0
            &&& post.devices.names(post.tables.payload_of(x).base)
            &&& post.devices.holder@.contains_key(post.tables.payload_of(x).base)
            &&& post.devices.holder@[post.tables.payload_of(x).base] == x
        } by {
            if x == n {
                assert(pre.tables.is_cap(&pre.list, i));
            } else {
                assert(x != i);
                Self::lemma_caps_frame(pre, post, i, n, x);
                assert(pre.tables.is_cap(&pre.list, x));
                if pp.kind is Device && post.tables.payload_of(x).base == base {
                    assert(pre.tables.is_cap(&pre.list, i));
                    lemma_device_cap_unique(&pre.list, &pre.tables, &pre.devices, i, x);
                }
            }
        }
    }

    /// Each block's holders after node i is renamed n.
    pub open spec fn moved_holders(holders: IMap<BlockRef, Set<usize>>, i: usize, n: usize) -> IMap<BlockRef, Set<usize>> {
        IMap::new(
            |br: BlockRef| holders.contains_key(br),
            |br: BlockRef| if holders[br].contains(i) { holders[br].remove(i).insert(n) } else { holders[br] },
        )
    }

    /// What a move does to the fields the view reads.
    pub open spec fn move_step(pre: Self, post: Self, i: usize, n: usize) -> bool {
        &&& Self::caps_frame(pre, post, i, n)
        &&& pre.is_cap(i)
        &&& !pre.list.nodes@[n as int].live
        &&& !post.list.nodes@[i as int].live
        &&& post.list.nodes@[n as int].live
        &&& post.list.nodes@[n as int].kind is Capability
        &&& n % 4096 != 0
        &&& n % 4096 < NODES_PER_PAGE
        &&& pre.tables.owner@.contains_key(page_of(n))
        &&& post.payload_of(n) == pre.payload_of(i)
        &&& post.list.wf()
        &&& post.list.parent@ == moved_parent(pre.list.parent@, i, n)
    }

    /// Every capability still names a block.
    proof fn lemma_move_caps_wf(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
    {
        assert(pre.tables.is_cap(&pre.list, i));
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) implies {
            &&& cap_wf(post.tables.payload_of(x))
            &&& control_named(post.tables.payload_of(x))
        } by {
            if x != n {
                assert(x != i);
                Self::lemma_caps_frame(pre, post, i, n, x);
                assert(post.is_cap(x));
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
    }

    /// Every capability, parent and holding of pre is in post under its new name, when the move stays in
    /// one table.
    proof fn lemma_move_simulates(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            pre.tables.owner@[page_of(n)].0 == pre.tables.owner@[page_of(i)].0,
        ensures
            simulates(
                pre.view(),
                post.view(),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
                |x: NodeId| rename(x, i, n),
            ),
    {
        let (a, b) = (pre.view(), post.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let f = |x: NodeId| rename(x, i, n);
        assert forall|x: NodeId| #[trigger] pre.is_cap(x) implies {
            &&& live(x)
            &&& post.is_cap(f(x))
            &&& post.payload_of(f(x)) == pre.payload_of(x)
            &&& pre.tables.owner@[page_of(f(x))].0 == pre.tables.owner@[page_of(x)].0
        } by {
            pre.lemma_slot_bound(x);
            if x != i {
                assert(x != n);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(pre.is_cap(h.1));
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            pre.list.lemma_parent_live(x);
            assert(x != n);
            assert(a.parent[x] != n);
            lemma_moved_parent(pre.list.parent@, i, n, x);
        }
        assert(simulates(a, b, live, f));
    }

    /// Every capability, parent and holding of post was in pre under its old name, the moved one held
    /// by the table it came from.
    proof fn lemma_move_simulated(pre: Self, post: Self, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
        ensures
            simulates_claim(
                post.view(),
                pre.view(),
                |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live,
                |x: NodeId| rename(x, n, i),
                pre.tables.owner@[page_of(n)].0,
                pre.tables.owner@[page_of(i)].0,
            ),
    {
        let (dst, src) = (pre.tables.owner@[page_of(n)].0, pre.tables.owner@[page_of(i)].0);
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live;
        let f = |x: NodeId| rename(x, n, i);
        pre.lemma_slot_bound(n);
        pre.lemma_slot_bound(i);
        assert forall|x: NodeId| #[trigger] post.is_cap(x) implies {
            &&& live(x)
            &&& pre.is_cap(f(x))
            &&& pre.payload_of(f(x)) == post.payload_of(x)
        } by {
            pre.lemma_slot_bound(x);
            if x != n {
                assert(x != i);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1)
            && (b.held.contains((h.0, f(h.1))) || (h.0 == dst && b.held.contains((src, f(h.1))))) by {
            assert(post.is_cap(h.1));
            if h.1 == n {
                assert(pre.is_cap(i));
                assert(b.held.contains((src, i)));
            }
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            post.list.lemma_parent_live(x);
            assert(x != i);
            let old_x = f(x);
            assert(old_x < NODE_SPACE && pre.list.nodes@[old_x as int].live) by {
                if x != n {
                    assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                }
            }
            lemma_moved_parent_back(pre.list.parent@, i, n, x);
            pre.list.lemma_parent_live(old_x);
            assert(pre.list.parent@[old_x] != n);
        }
        assert(simulates_claim(a, b, live, f, dst, src));
    }

    /// The view of the step: the capability the caller held has a new name, and that name is the only
    /// thing that went; reach is the same in both directions.
    proof fn lemma_move_discharges(pre: Self, post: Self, root: usize, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            pre.tables.owner@[page_of(i)].0 == root,
            pre.tables.owner@[page_of(n)].0 == root,
        ensures
            post.view().holds(root, n),
            forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o),
            discharges(pre.view(), post.view(), root, Effect::Local),
    {
        let (a, b) = (pre.view(), post.view());
        Self::lemma_move_simulates(pre, post, i, n);
        Self::lemma_move_simulated(pre, post, i, n);
        lemma_simulates_claim_self(b, a, |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live, |x: NodeId| rename(x, n, i), root);
        assert(a.holds(root, i));
        assert(post.is_cap(n));
        assert(b.holds(root, n));
        assert forall|r: ObjectId, o: ObjectId| #[trigger] b.reach(r, o) == a.reach(r, o) by {
            if b.reach(r, o) {
                lemma_simulates_reach(b, a, |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live, |x: NodeId| rename(x, n, i), r, o);
            }
            if a.reach(r, o) {
                lemma_simulates_reach(a, b, |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live, |x: NodeId| rename(x, i, n), r, o);
            }
        }
        assert forall|x: NodeId| #[trigger] State::removed(a, b, x) implies may_remove(a, root, Effect::Local, x) by {
            if x != i {
                assert(x != n);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|o: ObjectId| #[trigger] State::changed(a, b, o) implies may_change(a, Effect::Local, o) by {
            assert((a.contents)(o) == (b.contents)(o));
        }
    }

    /// The view of a claim's step: the caller, holding control over the process named by c, took node i
    /// from that process's table as n in its own. Only i went, and nobody's reach grew, since the caller
    /// reached what i covers through c already.
    proof fn lemma_claim_discharges(pre: Self, post: Self, root: usize, c: usize, i: usize, n: usize)
        requires
            Self::move_step(pre, post, i, n),
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            pre.payload_of(c).rights & right_bit(Right::Control) != 0,
            pre.tables.owner@[page_of(i)].0 == pre.payload_of(c).base,
            pre.tables.owner@[page_of(n)].0 == root,
        ensures
            discharges(pre.view(), post.view(), root, Effect::Claim { cap: c, from: i }),
    {
        let (a, b) = (pre.view(), post.view());
        Self::lemma_move_simulated(pre, post, i, n);
        assert(a.holds_right(root, c, Right::Control));
        assert(a.names[c] == pre.payload_of(c).base);
        assert(a.holds(a.names[c], i));
        assert forall|x: NodeId| #[trigger] State::removed(a, b, x) implies x == i by {
            if x != i {
                assert(x != n);
                Self::lemma_caps_frame(pre, post, i, n, x);
            }
        }
        assert forall|o: ObjectId| #[trigger] (b.contents)(o) == (a.contents)(o) by {}
        lemma_simulates_claim_discharges(
            a,
            b,
            root,
            c,
            i,
            |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live,
            |x: NodeId| rename(x, n, i),
        );
    }
}

/// Where moved_parent puts a parent entry, renamed.
proof fn lemma_moved_parent(p: Map<usize, usize>, i: usize, n: usize, x: usize)
    requires
        p.contains_key(x),
        x != n,
        p.dom().finite(),
    ensures
        moved_parent(p, i, n).contains_key(rename(x, i, n)),
        moved_parent(p, i, n)[rename(x, i, n)] == rename(p[x], i, n),
{
    let q = moved_parent(p, i, n);
    if x == i {
        assert(rename(rename(x, i, n), n, i) == x);
    }
}

/// And which entry an entry of moved_parent came from.
proof fn lemma_moved_parent_back(p: Map<usize, usize>, i: usize, n: usize, x: usize)
    requires
        moved_parent(p, i, n).contains_key(x),
        p.dom().finite(),
    ensures
        p.contains_key(rename(x, n, i)),
        moved_parent(p, i, n)[x] == rename(p[rename(x, n, i)], i, n),
{
}

} // verus!
