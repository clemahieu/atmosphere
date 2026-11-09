//! Revoking a capability, a bounded number of steps per kernel entry. A step finds a node of its run with
//! no children, undoes what that node's kind holds, and unlinks it, so revoke removes exactly the
//! capability's lineage, leaf first. See design/revoke-by-depth-first-list/.
use vstd::prelude::*;

verus! {

use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::space::*;
use crate::capability::refs::*;
use crate::capability::table::*;
use crate::capability::process::*;
use crate::capability::thread::*;
use crate::capability::thread::ThreadState;
use crate::capability::view::*;
use crate::define::*;

/// How many steps a revoke does per kernel entry. No wait happens under the lock, so a revoke returns
/// and is called again. It is above the core count so the revoker outruns any number of deriving
/// threads, each core getting one entry per turn: reasoned in the design, not proven, since this
/// theorem is about safety.
pub const REVOKE_BUDGET: usize = 64;

pub proof fn lemma_budget_above_cores()
    ensures
        REVOKE_BUDGET > NUM_CPUS,
{
}

/// What a revoke did.
pub enum RevokeStep {
    /// Nothing changed: the index names no capability.
    Refused,
    /// The capability's run is empty.
    Done,
    /// Its budget ran out with some of the run left. Revoke again to go on.
    Again,
    /// The flush epoch is at its limit with some of the run left, after 2^64 unmaps. A further step could
    /// not record its staleness, so none was taken.
    Exhausted,
}

impl CapKernel {
    /// Undoes what node n holds by its kind, before it is unlinked. Every arm meets this one spec: it
    /// changes no node's liveness and keeps the tables whole, and only what n itself held goes. A
    /// hidden node drops its block's reference and nothing more: a leaf stays in its root entry, inert,
    /// until its own retype frees it, and a table page's was cut from its parent by cut_hidden_table or
    /// detach_stale first. A capability's reference goes with atmo-6x9.16.22. A mapping node
    /// records its unmap, clears its entry and drops its reference. A binding node, a thread's binding to
    /// its process, leaves the thread with no process and drops its reference on the process's block.
    pub fn unlink_arm(&mut self, n: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            n != old(self).list.seq@[0],
            old(self).list.nodes@[n as int].kind is Mapping ==> old(self).flush_epoch < usize::MAX,
        ensures
            final(self).tables.wf(&old(self).list),
            final(self).blocks.wf(),
            final(self).list == old(self).list,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            final(self).devices == old(self).devices,
            final(self).stale_epoch.wf(),
            final(self).tlb_wf(),
            mapped_wf(final(self).mapped@, final(self).mappings@),
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> {
                &&& final(self).flush_epoch == old(self).flush_epoch
                &&& final(self).tlb == old(self).tlb
                &&& final(self).iommus == old(self).iommus
                &&& final(self).mapped == old(self).mapped
                &&& final(self).stale_epoch == old(self).stale_epoch
            },
            old(self).list.nodes@[n as int].kind is Mapping ==> Self::mapping_stale_noted(*old(self), *final(self), n),
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.roots@.dom() == old(self).tables.roots@.dom(),
            forall|x: usize| x != n ==> #[trigger] final(self).tables.payload_of(x) == old(self).tables.payload_of(x),
            final(self).tables == old(self).tables,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> final(self).table_pages == old(self).table_pages,
            old(self).is_cap(n) && old(self).payload_of(n).kind is Frame ==> {
                let br = block_ref(&old(self).blocks, old(self).payload_of(n).base / 4096);
                &&& blocks_refs_changed(
                    &old(self).blocks,
                    &final(self).blocks,
                    br,
                    (block_refs(&old(self).blocks, br) - 1) as usize,
                    block_dead(&old(self).blocks, br) || block_refs(&old(self).blocks, br) == 1,
                )
                &&& final(self).holders@ == old(self).holders@.insert(br, old(self).holders@[br].remove(n))
            },
            old(self).is_cap(n) && old(self).payload_of(n).kind is Space ==> {
                let s = old(self).payload_of(n).base;
                let br = BlockRef::Small(s / 4096);
                &&& blocks_refs_changed(
                    &old(self).blocks,
                    &final(self).blocks,
                    br,
                    (block_refs(&old(self).blocks, br) - 1) as usize,
                    block_dead(&old(self).blocks, br) || block_refs(&old(self).blocks, br) == 1,
                )
                &&& final(self).holders == old(self).holders
                &&& final(self).spaces.holders@ == old(self).spaces.holders@.insert(s, old(self).spaces.holders@[s].remove(n))
            },
            !(old(self).is_cap(n) && old(self).payload_of(n).kind is Space) ==> final(self).spaces == old(self).spaces,
            old(self).is_cap(n) && old(self).payload_of(n).kind is Thread ==> {
                let t = old(self).payload_of(n).base;
                let br = BlockRef::Small(t / 4096);
                &&& blocks_refs_changed(
                    &old(self).blocks,
                    &final(self).blocks,
                    br,
                    (block_refs(&old(self).blocks, br) - 1) as usize,
                    block_dead(&old(self).blocks, br) || block_refs(&old(self).blocks, br) == 1,
                )
                &&& final(self).holders == old(self).holders
                &&& final(self).threads.holders@ == old(self).threads.holders@.insert(t, old(self).threads.holders@[t].remove(n))
            },
            !(old(self).is_cap(n) && old(self).payload_of(n).kind is Thread) && !(old(self).list.nodes@[n as int].kind is Binding)
                ==> final(self).threads == old(self).threads,
            !(old(self).list.nodes@[n as int].kind is Binding) ==> final(self).threads.records == old(self).threads.records,
            old(self).list.nodes@[n as int].kind is Binding ==> Self::unbound(*old(self), *final(self), n),
            old(self).is_cap(n) && old(self).payload_of(n).kind is Process ==> {
                let p = old(self).payload_of(n).base;
                let br = BlockRef::Small(p / 4096);
                &&& blocks_refs_changed(
                    &old(self).blocks,
                    &final(self).blocks,
                    br,
                    (block_refs(&old(self).blocks, br) - 1) as usize,
                    block_dead(&old(self).blocks, br) || block_refs(&old(self).blocks, br) == 1,
                )
                &&& final(self).holders == old(self).holders
                &&& final(self).processes.bound == old(self).processes.bound
                &&& final(self).processes.holders@ == old(self).processes.holders@.insert(p, old(self).processes.holders@[p].remove(n))
            },
            !(old(self).is_cap(n) && old(self).payload_of(n).kind is Process) && !(old(self).list.nodes@[n as int].kind is Binding)
                ==> final(self).processes == old(self).processes,
            final(self).processes.records == old(self).processes.records,
            final(self).processes.spare == old(self).processes.spare,
            final(self).spaces.roots == old(self).spaces.roots,
            final(self).spaces.records == old(self).spaces.records,
            final(self).spaces.loaded == old(self).spaces.loaded,
            final(self).spaces.kernel_entries == old(self).spaces.kernel_entries,
            final(self).spaces.bound == old(self).spaces.bound,
            old(self).list.nodes@[n as int].kind is Mapping ==> Self::mapping_unlinked(*old(self), *final(self), n),
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> {
                &&& Self::same_tree(*old(self), *final(self))
                &&& final(self).mappings == old(self).mappings
            },
            old(self).list.nodes@[n as int].kind is Hidden ==> {
                &&& blocks_refs_changed(&old(self).blocks, &final(self).blocks, BlockRef::Small(n / 4096), 0, true)
                &&& final(self).holders == old(self).holders
            },
            !(old(self).is_cap(n) && (old(self).payload_of(n).kind is Frame || old(self).payload_of(n).kind is Space
                || old(self).payload_of(n).kind is Thread || old(self).payload_of(n).kind is Process))
                && !(old(self).list.nodes@[n as int].kind is Hidden) && !(old(self).list.nodes@[n as int].kind is Mapping)
                && !(old(self).list.nodes@[n as int].kind is Binding) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
            },
    {
        let ghost pre = *old(self);
        proof {
            self.list.lemma_live_valid(n);
        }
        let node = self.list.get(n);
        match node.kind {
            NodeKind::Hidden => {
                proof {
                    pre.lemma_hidden_block(n);
                }
                // The block's one reference was the hidden node's, so it is dead at once.
                drop_block_ref(&mut self.blocks, BlockRef::Small(n / 4096));
            },
            NodeKind::Capability => {
                proof {
                    assert(pre.is_cap(n));
                }
                let payload = self.tables.payload_at(&self.list, n);
                match payload.kind {
                    CapKind::Frame => {
                        proof {
                            lemma_holder_refs(&pre.list, &pre.tables, &pre.blocks, &pre.zeroing, pre.holders@, n);
                        }
                        let br = locate(&self.blocks, payload.base / 4096);
                        drop_block_ref(&mut self.blocks, br);
                        self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
                    },
                    CapKind::Space => {
                        proof {
                            pre.lemma_space_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / 4096));
                        self.spaces.holders = Ghost(pre.spaces.holders@.insert(payload.base, pre.spaces.holders@[payload.base].remove(n)));
                    },
                    CapKind::Thread => {
                        proof {
                            pre.lemma_thread_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / 4096));
                        self.threads.holders = Ghost(pre.threads.holders@.insert(payload.base, pre.threads.holders@[payload.base].remove(n)));
                    },
                    CapKind::Process => {
                        proof {
                            pre.lemma_process_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / 4096));
                        self.processes.holders = Ghost(pre.processes.holders@.insert(payload.base, pre.processes.holders@[payload.base].remove(n)));
                    },
                    _ => {},
                }
            },
            NodeKind::Mapping => { self.clear_mapping(n); },
            NodeKind::Binding => { self.unbind(n); },
        }
        proof {
            if !(node.kind is Mapping) {
                Self::lemma_tlb_same(pre, *self);
            }
        }
    }

    /// What a revoke of the capability at index i of the table at root did when it was not refused: the
    /// index names a capability, at most REVOKE_BUDGET nodes of its run went, no mapping appeared, no
    /// node changed its parent, the threads bound are those that were whose bindings are still live,
    /// and the step discharges the revoke's effect.
    pub open spec fn cap_revoking(pre: Self, post: Self, root: usize, i: usize) -> bool {
        let c = pre.tables.node_of(root, i);
        &&& pre.tables.has_slot(&pre.list, root, i)
        &&& pre.is_cap(c)
        &&& Self::mappings_shrunk(pre, post)
        &&& pre.list.seq@.len() - post.list.seq@.len() <= REVOKE_BUDGET
        &&& post.list.parent == pre.list.parent
        &&& discharges(pre.view(), post.view(), root, Effect::Revoke { cap: c })
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).restrict(live_nodes(&post.list))
    }

    /// What a revoke of the capability at index i of the table at root did when it finished: as
    /// cap_revoking says, and the capability has no child left.
    pub open spec fn cap_revoked(pre: Self, post: Self, root: usize, i: usize) -> bool {
        let c = pre.tables.node_of(root, i);
        &&& Self::cap_revoking(pre, post, root, i)
        &&& post.list.childless(c)
        &&& forall|x: usize| !#[trigger] post.list.is_child(c, x)
    }

    /// Revokes the capability at index i of the table at root, for at most REVOKE_BUDGET steps. The
    /// index comes from user space, so it can be refused. Its own slot can leave the table during the
    /// call, if the leaf holding it is in its run, so the steps name its node instead.
    pub fn revoke(&mut self, root: usize, i: usize) -> (ret: RevokeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused == !(old(self).tables.has_slot(&old(self).list, root, i) && old(self).is_cap(old(self).tables.node_of(root, i))),
            ret is Refused ==> *final(self) == *old(self),
            old(self).flush_epoch == usize::MAX ==> *final(self) == *old(self),
            ret is Exhausted ==> final(self).flush_epoch == usize::MAX,
            !(ret is Refused) ==> Self::cap_revoking(*old(self), *final(self), root, i),
            !(ret is Refused) ==> (ret is Done == final(self).list.childless(old(self).tables.node_of(root, i))),
            ret is Done ==> Self::cap_revoked(*old(self), *final(self), root, i),
    {
        let ghost pre = *old(self);
        let c = match self.tables.lookup(&self.list, root, i) {
            Some(found) => found.0,
            None => { return RevokeStep::Refused; },
        };
        let node = self.list.get(c);
        let kind_ok = match node.kind {
            NodeKind::Capability => node.live,
            _ => false,
        };
        if !kind_ok {
            return RevokeStep::Refused;
        }
        proof {
            pre.lemma_slot(root, i);
            assert(pre.tables.is_cap(&pre.list, c));
            pre.lemma_slot_bound(c);
            pre.lemma_no_change_discharges_revoke(root, c);
            lemma_bound_threads_live(&pre.list, &pre.tables);
        }
        let mut steps = 0;
        while steps != REVOKE_BUDGET && self.flush_epoch != usize::MAX
            invariant
                steps <= REVOKE_BUDGET,
                self.wf(),
                self.cores == pre.cores,
                pre == *old(self),
                pre.flush_epoch == usize::MAX ==> *self == pre,
                Self::mappings_shrunk(pre, *self),
                pre.tables.has_slot(&pre.list, root, i),
                c == pre.tables.node_of(root, i),
                c < NODE_SPACE,
                self.is_cap(c),
                self.tables.owner == pre.tables.owner,
                self.list.parent == pre.list.parent,
                pre.list.seq@.len() - self.list.seq@.len() == steps,
                pre.tables.owner@[page_of(c)].0 == root,
                pre.is_cap(c),
                discharges(pre.view(), self.view(), root, Effect::Revoke { cap: c }),
                bound_threads(&self.list, &self.tables) == bound_threads(&pre.list, &pre.tables).restrict(live_nodes(&self.list)),
            decreases REVOKE_BUDGET - steps,
        {
            let ghost mid = *self;
            if self.revoke_step(Ghost(root), c) {
                proof {
                    assert(self.view() == mid.view());
                }
                return RevokeStep::Done;
            }
            proof {
                lemma_revoke_steps_compose(pre.view(), mid.view(), self.view(), root, c);
                let r = choose|r: usize| #[trigger] revoked_one(mid.list, self.list, c, r)
                    && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(mid, *self, r))
                    && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(mid, *self, r))
                    && (mid.hidden_table(r) ==> Self::table_unlinked(mid, *self, r))
                    && (mid.list.nodes@[r as int].kind is Binding ==> bound_threads(&self.list, &self.tables)
                        == bound_threads(&mid.list, &mid.tables).remove(r))
                    && (!(mid.list.nodes@[r as int].kind is Binding) ==> bound_threads(&self.list, &self.tables)
                        == bound_threads(&mid.list, &mid.tables));
                Self::lemma_revoke_bound_threads(bound_threads(&pre.list, &pre.tables), mid, *self, r);
            }
            steps = steps + 1;
        }
        if self.list.is_childless(c) {
            RevokeStep::Done
        } else if self.flush_epoch == usize::MAX {
            RevokeStep::Exhausted
        } else {
            RevokeStep::Again
        }
    }

    /// One step of revoking capability c, which root's table holds. Returns whether c's run was empty.
    pub fn revoke_step(&mut self, Ghost(root): Ghost<usize>, c: usize) -> (done: bool)
        requires
            old(self).wf(),
            c < NODE_SPACE,
            old(self).is_cap(c),
            old(self).tables.owner@[page_of(c)].0 == root,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::mappings_shrunk(*old(self), *final(self)),
            final(self).is_cap(c),
            final(self).tables.owner == old(self).tables.owner,
            final(self).list.parent == old(self).list.parent,
            done == old(self).list.childless(c),
            done ==> *final(self) == *old(self),
            done ==> forall|x: usize| !#[trigger] old(self).list.is_child(c, x),
            !done ==> final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            !done ==> exists|r: usize| #[trigger] revoked_one(old(self).list, final(self).list, c, r)
                && (old(self).list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(*old(self), *final(self), r))
                && (old(self).list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(*old(self), *final(self), r))
                && (old(self).hidden_table(r) ==> Self::table_unlinked(*old(self), *final(self), r))
                && (old(self).list.nodes@[r as int].kind is Binding ==> bound_threads(&final(self).list, &final(self).tables)
                    == bound_threads(&old(self).list, &old(self).tables).remove(r))
                && (!(old(self).list.nodes@[r as int].kind is Binding) ==> bound_threads(&final(self).list, &final(self).tables)
                    == bound_threads(&old(self).list, &old(self).tables)),
            forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] final(self).list.nodes@[x].depth == old(self).list.nodes@[x].depth,
            forall|x: usize| #[trigger] final(self).is_cap(x) ==> old(self).is_cap(x),
            discharges(old(self).view(), final(self).view(), root, Effect::Revoke { cap: c }),
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_change_discharges_revoke(root, c);
        }
        let r = match self.list.leaf_of_run(c) {
            Some(found) => found,
            None => { return true; },
        };
        self.cut_hidden_table(r);
        let ghost cut = *self;
        self.unlink_arm(r);
        let ghost mid = *self;
        self.list.remove_leaf(r);
        proof {
            Self::lemma_revoke_step_wf(cut, mid, *self, root, c, r);
            assert(cut.view() == pre.view());
            if pre.hidden_table(r) {
                Self::lemma_cut_recorded_same(pre, cut, *self, r);
                Self::lemma_cut_shrunk(pre, cut, r);
                Self::lemma_shrunk_compose(pre, cut, *self);
                assert(Self::table_unlinked(pre, *self, r));
            }
            assert(revoked_one(pre.list, self.list, c, r));
        }
        false
    }

    /// The state after the leaf r of c's run has its arm unlinked and its node removed: well formed,
    /// with r's capability and its mapping gone and every other capability as it was.
    proof fn lemma_revoke_step_wf(pre: Self, mid: Self, post: Self, root: usize, c: usize, r: usize)
        requires
            pre.wf(),
            mid.tables.roots@.dom() == pre.tables.roots@.dom(),
            c < NODE_SPACE,
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            r < NODE_SPACE,
            has(pre.list.seq@, r),
            pre.list.nodes@[r as int].live,
            r != pre.list.seq@[0],
            pre.list.d(r) > pre.list.d(c),
            pre.list.anc(r, (pre.list.d(r) - pre.list.d(c)) as nat) == c,
            pre.list.childless(r),
            pre.hidden_table(r) ==> pre.table_pages.records@[r].value().parent is None,
            mid.tables.wf(&pre.list),
            mid.blocks.wf(),
            mid.list == pre.list,
            mid.frames == pre.frames,
            mid.zeroing == pre.zeroing,
            mid.cores == pre.cores,
            mid.stale_epoch.wf(),
            mid.tlb_wf(),
            mapped_wf(mid.mapped@, mid.mappings@),
            pre.list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(pre, mid, r),
            mid.tables.owner == pre.tables.owner,
            forall|x: usize| x != r ==> #[trigger] mid.tables.payload_of(x) == pre.tables.payload_of(x),
            mid.tables == pre.tables,
            mid.table_pages.records == pre.table_pages.records,
            mid.table_pages.spare == pre.table_pages.spare,
            !(pre.list.nodes@[r as int].kind is Mapping) ==> mid.table_pages == pre.table_pages,
            pre.is_cap(r) && pre.payload_of(r).kind is Frame ==> {
                let br = block_ref(&pre.blocks, pre.payload_of(r).base / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &mid.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& mid.holders@ == pre.holders@.insert(br, pre.holders@[br].remove(r))
            },
            pre.is_cap(r) && pre.payload_of(r).kind is Space ==> {
                let s = pre.payload_of(r).base;
                let br = BlockRef::Small(s / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &mid.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& mid.holders == pre.holders
                &&& mid.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].remove(r))
            },
            !(pre.is_cap(r) && pre.payload_of(r).kind is Space) ==> mid.spaces == pre.spaces,
            pre.is_cap(r) && pre.payload_of(r).kind is Thread ==> {
                let t = pre.payload_of(r).base;
                let br = BlockRef::Small(t / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &mid.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& mid.holders == pre.holders
                &&& mid.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].remove(r))
            },
            !(pre.is_cap(r) && pre.payload_of(r).kind is Thread) && !(pre.list.nodes@[r as int].kind is Binding)
                ==> mid.threads == pre.threads,
            !(pre.list.nodes@[r as int].kind is Binding) ==> mid.threads.records == pre.threads.records,
            pre.list.nodes@[r as int].kind is Binding ==> Self::unbound(pre, mid, r),
            pre.is_cap(r) && pre.payload_of(r).kind is Process ==> {
                let p = pre.payload_of(r).base;
                let br = BlockRef::Small(p / 4096);
                &&& blocks_refs_changed(
                    &pre.blocks,
                    &mid.blocks,
                    br,
                    (block_refs(&pre.blocks, br) - 1) as usize,
                    block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1,
                )
                &&& mid.holders == pre.holders
                &&& mid.processes.bound == pre.processes.bound
                &&& mid.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].remove(r))
            },
            !(pre.is_cap(r) && pre.payload_of(r).kind is Process) && !(pre.list.nodes@[r as int].kind is Binding)
                ==> mid.processes == pre.processes,
            mid.processes.records == pre.processes.records,
            mid.processes.spare == pre.processes.spare,
            mid.spaces.roots == pre.spaces.roots,
            mid.spaces.records == pre.spaces.records,
            mid.spaces.loaded == pre.spaces.loaded,
            mid.spaces.kernel_entries == pre.spaces.kernel_entries,
            mid.spaces.bound == pre.spaces.bound,
            mid.devices == pre.devices,
            pre.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(pre, mid, r),
            !(pre.list.nodes@[r as int].kind is Mapping) ==> {
                &&& Self::same_tree(pre, mid)
                &&& mid.mappings == pre.mappings
            },
            pre.list.nodes@[r as int].kind is Hidden ==> {
                &&& blocks_refs_changed(&pre.blocks, &mid.blocks, BlockRef::Small(r / 4096), 0, true)
                &&& mid.holders == pre.holders
            },
            !(pre.is_cap(r) && (pre.payload_of(r).kind is Frame || pre.payload_of(r).kind is Space
                || pre.payload_of(r).kind is Thread || pre.payload_of(r).kind is Process))
                && !(pre.list.nodes@[r as int].kind is Hidden) && !(pre.list.nodes@[r as int].kind is Mapping)
                && !(pre.list.nodes@[r as int].kind is Binding) ==> {
                &&& mid.blocks == pre.blocks
                &&& mid.holders == pre.holders
            },
            post.cores == mid.cores,
            post.flush_epoch == mid.flush_epoch,
            post.tlb == mid.tlb,
            post.iommus == mid.iommus,
            post.mapped == mid.mapped,
            post.blocks == mid.blocks,
            post.tables == mid.tables,
            post.stale_epoch == mid.stale_epoch,
            post.frames == mid.frames,
            post.table_pages == mid.table_pages,
            post.spaces == mid.spaces,
            post.mappings == mid.mappings,
            post.zeroing == mid.zeroing,
            post.holders == mid.holders,
            post.devices == mid.devices,
            post.threads == mid.threads,
            post.processes == mid.processes,
            post.stop_ipis == mid.stop_ipis,
            post.list.wf(),
            post.list.nodes@.len() == pre.list.nodes@.len(),
            !post.list.nodes@[r as int].live,
            forall|x: int| 0 <= x < pre.list.nodes@.len() && x != r ==>
                #[trigger] post.list.nodes@[x].live == pre.list.nodes@[x].live,
            forall|x: int| 0 <= x < pre.list.nodes@.len() ==>
                #[trigger] post.list.nodes@[x].depth == pre.list.nodes@[x].depth,
            forall|x: int| 0 <= x < pre.list.nodes@.len() && x != r ==>
                #[trigger] post.list.nodes@[x].kind == pre.list.nodes@[x].kind,
            post.list.parent@ == pre.list.parent@,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            exists|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == r
                && post.list.seq@ == pre.list.seq@.remove(p),
        ensures
            post.wf(),
            Self::mappings_shrunk(pre, post),
            post.is_cap(c),
            revoked_one(pre.list, post.list, c, r),
            pre.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(pre, post, r),
            pre.list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(pre, post, r),
            forall|x: usize| #[trigger] post.is_cap(x) ==> pre.is_cap(x),
            discharges(pre.view(), post.view(), root, Effect::Revoke { cap: c }),
            pre.list.nodes@[r as int].kind is Binding
                ==> bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).remove(r),
            !(pre.list.nodes@[r as int].kind is Binding)
                ==> bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    {
        post.tables.lemma_wf_same_pages(&pre.list, &post.list);
        Self::lemma_revoke_step(pre, post, root, c, r);
        Self::lemma_delete_caps_wf(pre, post, r);
        assert(revoked_one(pre.list, post.list, c, r));
        let p = choose|p: int| 0 <= p < pre.list.seq@.len() && pre.list.seq@[p] == r
            && post.list.seq@ == pre.list.seq@.remove(p);
        assert(p != 0);
        assert(post.list.seq@[0] == pre.list.seq@[0]);
        lemma_parents_removed(pre.list, post.list, r);
        if pre.list.nodes@[r as int].kind is Mapping {
            assert(Self::mapping_unlinked(pre, post, r));
            assert(pre.mappings@.contains_key(r));
            pre.lemma_mapping_node(r);
            assert(mapping_wf(&pre.list, &pre.tables, tree_of(&pre.table_pages, &pre.spaces), &pre.blocks, pre.holders@, pre.mappings@, r));
            assert(pre.table_pages.maps@.contains_key(pre.mappings@[r].table));
            assert(post.table_pages.maps@.dom() =~= pre.table_pages.maps@.dom());
        }
        Self::lemma_revoke_hidden(pre, post, r);
        if pre.list.nodes@[r as int].kind is Hidden {
            Self::lemma_revoke_hidden_holders(pre, post, r);
            Self::lemma_same_tree_shrunk(pre, post);
            Self::lemma_bindings_caps_frame(pre, post, r, r);
        } else if pre.list.nodes@[r as int].kind is Mapping {
            Self::lemma_revoke_mapping_holders(pre, post, r);
            Self::lemma_unlinked_shrunk(pre, post, r);
            Self::lemma_stale_noted_same(pre, mid, post, r);
            Self::lemma_bindings_caps_frame(pre, post, r, r);
        } else if pre.list.nodes@[r as int].kind is Binding {
            Self::lemma_revoke_binding_holders(pre, post, r);
            Self::lemma_same_tree_shrunk(pre, post);
        } else {
            Self::lemma_delete_holders(pre, post, r);
            Self::lemma_same_tree_shrunk(pre, post);
            Self::lemma_bindings_caps_frame(pre, post, r, r);
        }
        Self::lemma_tlb_same(mid, post);
        assert(post.list.nodes@[c as int].live == pre.list.nodes@[c as int].live);
        Self::lemma_caps_frame(pre, post, r, r, c);
        assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) by {
            if x != r {
                Self::lemma_caps_frame(pre, post, r, r, x);
            }
        }
        if pre.list.nodes@[r as int].kind is Binding {
            assert forall|x: usize| x != r implies #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x) by {}
            Self::lemma_bound_threads_remove(pre, post, r);
        } else {
            Self::lemma_bound_threads_same(pre, post);
        }
    }

    /// A step that unlinks one node r and loses at most r from the bound threads, as a revoke step does,
    /// keeps them those of the state the revoke began in whose binding nodes are live.
    pub proof fn lemma_revoke_bound_threads(b0: Map<ObjectId, ObjectId>, mid: Self, post: Self, r: usize)
        requires
            mid.wf(),
            bound_threads(&mid.list, &mid.tables) == b0.restrict(live_nodes(&mid.list)),
            !post.list.nodes@[r as int].live,
            forall|x: int| 0 <= x < NODE_SPACE && x != r ==> #[trigger] post.list.nodes@[x].live == mid.list.nodes@[x].live,
            mid.list.nodes@[r as int].kind is Binding
                ==> bound_threads(&post.list, &post.tables) == bound_threads(&mid.list, &mid.tables).remove(r),
            !(mid.list.nodes@[r as int].kind is Binding)
                ==> bound_threads(&post.list, &post.tables) == bound_threads(&mid.list, &mid.tables),
        ensures
            bound_threads(&post.list, &post.tables) == b0.restrict(live_nodes(&post.list)),
    {
        broadcast use vstd::set::lemma_set_filter;
        let bm = bound_threads(&mid.list, &mid.tables);
        let bp = bound_threads(&post.list, &post.tables);
        let l = b0.restrict(live_nodes(&post.list));
        assert forall|t: usize| #[trigger] bp.dom().contains(t) == l.dom().contains(t) by {
            if t < NODE_SPACE && t != r {
                assert(post.list.nodes@[t as int].live == mid.list.nodes@[t as int].live);
            }
            assert(bm.dom().contains(t) == (b0.dom().contains(t) && live_nodes(&mid.list).contains(t)));
        }
        assert(bp =~= l);
    }

    /// A step that changes nothing, with the capability held, discharges a revoke of it.
    proof fn lemma_no_change_discharges_revoke(&self, root: usize, c: usize)
        requires
            self.is_cap(c),
            self.tables.owner@[page_of(c)].0 == root,
        ensures
            discharges(self.view(), self.view(), root, Effect::Revoke { cap: c }),
    {
        assert(self.view().holds(root, c));
        assert(self.view().names.contains_key(c));
    }

    /// The holders and the blocks after hidden node n goes with its block's one reference: no frame
    /// changed, the block was no holder's key, and it is dead at zero as its node is dead. It was a
    /// leaf's or a table page's, and the other kind's blocks are as they were.
    pub proof fn lemma_revoke_hidden_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Hidden,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.table_pages == pre.table_pages,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.mappings == pre.mappings,
            pre.hidden_table(n) ==> pre.table_pages.records@[n].value().parent is None,
            blocks_refs_changed(&pre.blocks, &post.blocks, BlockRef::Small(n / 4096), 0, true),
            post.holders == pre.holders,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
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
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let br = BlockRef::Small(n / 4096);
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies pre.list.parent@[m] != n by {
            pre.lemma_mapping_node(m);
        }
        Self::lemma_mapping_parents_kept(pre, post, n, n);
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
        }
        Self::lemma_mappings_same_tree(pre, post);
        pre.lemma_hidden_block(n);
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        // The block is a leaf's or a table page's, so no space's, thread's or process's.
        assert(!(pre.blocks.pages@[(n / 4096) as int].object is Space));
        assert(!(pre.blocks.pages@[(n / 4096) as int].object is Thread));
        assert(!(pre.blocks.pages@[(n / 4096) as int].object is Process));
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, 0, true);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, 0, true);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, 0, true);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, n / 4096, 0, true);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, n / 4096, 0, true);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, n / 4096, 0, true);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) && l != n implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
        }
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && t != n implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
        }
        if pre.tables.owner@.contains_key(n) {
            lemma_leaf_blocks_leaf_dropped(&pre.list, &post.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, n);
            lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, 0, true);
        } else {
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, n / 4096, 0, true);
            lemma_table_page_dropped(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, n);
        }
    }

    /// The invariant's parts after binding node n goes with its thread's process and its reference on the
    /// process's block: no capability, mapping or frame changed, only that block's count did, and the
    /// thread keeps its core.
    pub proof fn lemma_revoke_binding_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Binding,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.tables == pre.tables,
            post.spaces == pre.spaces,
            post.table_pages == pre.table_pages,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            Self::unbound(pre, post, n),
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
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
            bindings_wf(&post.list, &post.threads, &post.processes),
            binding_parents(&post.list, &post.tables, &post.threads),
            current_wf(post.cores@, post.threads.records@),
    {
        reveal(thread_bound);
        let t = n;
        Self::lemma_binding_parents_caps_frame(pre, post, n, n);
        pre.lemma_bound_process(t);
        let p = pre.threads.records@[t].value().process->Some_0;
        let br = BlockRef::Small(p / 4096);
        let refs = (block_refs(&pre.blocks, br) - 1) as usize;
        let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_processes(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        assert(!pre.holders@.contains_key(br)) by {
            if pre.holders@.contains_key(br) {
                assert(pre.blocks.pages@[(p / 4096) as int].object is Frame);
            }
        }
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / 4096, refs, dead);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / 4096, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, refs, dead);
        // Node n is a thread's base, so no leaf's and no table page's.
        assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        assert(pre.blocks.pages@[(t / 4096) as int].object is Thread);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
            assert(pre.blocks.pages@[(l / 4096) as int].object is TableLeaf);
            assert(l != n);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / 4096, refs, dead);
        assert forall|u: usize| #[trigger] pre.table_pages.maps@.contains_key(u) implies {
            &&& post.list.nodes@[u as int].live == pre.list.nodes@[u as int].live
            &&& post.list.nodes@[u as int].kind == pre.list.nodes@[u as int].kind
        } by {
            pre.lemma_table_page_valid(u);
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, u));
            assert(u != n);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_record_written(&post.list, &post.tables, &pre.threads, &post.threads, &post.blocks, t);
        lemma_processes_same_caps(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks);
        lemma_processes_bound_dropped(&post.list, &post.tables, &pre.processes, &post.processes, &pre.blocks, &post.blocks, p, t);
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            let c = pre.list.parent@[m];
            assert(c != n);
            Self::lemma_caps_frame(pre, post, n, n, c);
        }
        Self::lemma_mappings_same_tree(pre, post);
        assert forall|x: usize| x < NODE_SPACE && x != t implies {
            &&& (#[trigger] post.list.nodes@[x as int]).live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        } by {}
        lemma_bindings_unbound(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes, t, p);
        assert(current_wf(post.cores@, post.threads.records@)) by {
            reveal(current_wf);
            assert forall|c: int, x: usize| 0 <= c < NUM_CPUS && #[trigger] runs(post.cores@, c, x) implies {
                &&& post.threads.records@.contains_key(x)
                &&& post.threads.records@[x].value().state == (ThreadState::Running { core: c as usize })
            } by {
                assert(runs(pre.cores@, c, x));
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().state is Running implies {
                let e = post.threads.records@[x].value().state->Running_core;
                &&& e < NUM_CPUS
                &&& post.cores@[e as int].current_thread == Some(x)
            } by {
                assert(pre.threads.records@.contains_key(x));
                assert(post.threads.records@[x].value().state == pre.threads.records@[x].value().state);
            }
            assert forall|x: usize| #[trigger] post.threads.records@.contains_key(x) && post.threads.records@[x].value().pending_stop
                implies post.threads.records@[x].value().state is Running by {
                assert(pre.threads.records@.contains_key(x));
            }
        }
    }

    /// The invariant's parts after mapping node n goes with its entry and its reference: the entry is
    /// empty, nothing above level 1 changed, its block's count fell by one, dead at zero, and no other
    /// node, capability or holder changed.
    pub proof fn lemma_revoke_mapping_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.tables == pre.tables,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.table_pages.records == pre.table_pages.records,
            post.table_pages.spare == pre.table_pages.spare,
            Self::mapping_unlinked(pre, post, n),
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
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        Self::lemma_revoke_mapping_blocks(pre, post, n);
        Self::lemma_revoke_mapping_tables(pre, post, n);
        Self::lemma_revoke_mapping_mappings(pre, post, n);
    }

    /// The holders and the blocks after mapping node n goes: it held its frame's block alone, and no
    /// capability changed.
    proof fn lemma_revoke_mapping_blocks(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.tables == pre.tables,
            Self::mapping_unlinked(pre, post, n),
        ensures
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let m = pre.mappings@[n];
        let br = block_ref(&pre.blocks, m.frame);
        let refs = (block_refs(&pre.blocks, br) - 1) as usize;
        let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
        assert(pre.mappings@.contains_key(n));
        pre.lemma_mapping_node(n);
        assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        pre.lemma_unhidden_not_owned(n);
        Self::lemma_same_leaf_nodes(pre, post, n, n);
        lemma_holders_mapping_dropped(&pre.list, &pre.tables, &post.list, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, n, br);
        lemma_zeroing_typed_refs_changed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, br, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && p / 4096 < NUM_PAGES implies {
            &&& !(post.blocks.pages@[(p / 4096) as int].kind is Free)
            &&& post.blocks.pages@[(p / 4096) as int].kind is Member
                ==> post.blocks.pages@[post.blocks.pages@[(p / 4096) as int].base as int].object is TablePage
                    || post.blocks.pages@[post.blocks.pages@[(p / 4096) as int].base as int].object is Space
            &&& !(post.blocks.pages@[(p / 4096) as int].object is Frame)
        } by {
            assert(pre.list.pages@.dom().contains(p));
        }
        assert forall|x: BlockRef| #[trigger] post.holders@.contains_key(x) == pre.holders@.contains_key(x) by {}
        lemma_objects_refs_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, post.holders@, br, refs, dead);
        lemma_leaf_blocks_refs_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, br, refs, dead);
    }

    /// The table pages, spaces and links after mapping node n goes: its frame's block is no table page's
    /// nor space's, and the one entry emptied is at level 1, below every link.
    proof fn lemma_revoke_mapping_tables(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.tables == pre.tables,
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.table_pages.records == pre.table_pages.records,
            post.table_pages.spare == pre.table_pages.spare,
            Self::mapping_unlinked(pre, post, n),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let m = pre.mappings@[n];
        let br = block_ref(&pre.blocks, m.frame);
        let refs = (block_refs(&pre.blocks, br) - 1) as usize;
        let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
        assert(pre.mappings@.contains_key(n));
        pre.lemma_mapping_node(n);
        assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
        assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, m.table));
        reveal(entries_cleared);
        pre.lemma_unhidden_not_table_page(n);
        Self::lemma_same_table_nodes(pre, post, n, n);
        if let BlockRef::Small(x) = br {
            assert(pre.blocks.pages@[x as int].object is Frame);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        assert forall|i: usize| #![trigger post.table_pages.maps@[m.table].value()[i]] i < 512 && i != m.entry
            implies post.table_pages.maps@[m.table].value()[i] == pre.table_pages.maps@[m.table].value()[i] by {
            assert(b.entry(m.table, i) == a.entry(m.table, i));
        }
        lemma_table_pages_entry_cleared(&post.list, &pre.table_pages, &post.table_pages, &post.blocks, m.table, m.entry);
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        assert(b.maps.dom() =~= a.maps.dom());
        lemma_links_entry_cleared(a, b, m.table, m.entry);
    }

    /// The mappings after mapping node n goes: every other mapping's entry, node, parent and holding
    /// are as they were, and the entry emptied was n's alone.
    proof fn lemma_revoke_mapping_mappings(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is Mapping,
            !post.list.nodes@[n as int].live,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.tables == pre.tables,
            post.spaces == pre.spaces,
            post.table_pages.records == pre.table_pages.records,
            Self::mapping_unlinked(pre, post, n),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(b.maps.dom() =~= a.maps.dom());
        let m = pre.mappings@[n];
        let br = block_ref(&pre.blocks, m.frame);
        assert(pre.mappings@.contains_key(n));
        pre.lemma_mapping_node(n);
        assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, n));
        reveal(entries_cleared);
        assert forall|x: usize| #[trigger] post.mappings@.contains_key(x)
            implies mapping_wf(&post.list, &post.tables, b, &post.blocks, post.holders@, post.mappings@, x) by {
            assert(pre.mappings@.contains_key(x));
            assert(x != n);
            pre.lemma_mapping_node(x);
            assert(mapping_wf(&pre.list, &pre.tables, a, &pre.blocks, pre.holders@, pre.mappings@, x));
            let mx = pre.mappings@[x];
            let c = pre.list.parent@[x];
            assert(c != n);
            Self::lemma_caps_frame(pre, post, n, n, c);
            assert(!(mx.table == m.table && mx.entry == m.entry));
            assert(b.entry(mx.table, mx.entry) == a.entry(mx.table, mx.entry));
            assert(b.record(mx.table) == a.record(mx.table));
            assert(post.holders@[block_ref(&pre.blocks, mx.frame)].contains(x));
            assert forall|k: BlockRef| post.holders@.contains_key(k) && #[trigger] post.holders@[k].contains(x)
                implies k == block_ref(&post.blocks, mx.frame) by {
                assert(pre.holders@[k].contains(x));
            }
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Mapping
            implies post.mappings@.contains_key(x) by {
            assert(x != n);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Mapping);
        }
        assert forall|t: usize, e: usize| #[trigger] frame_slot(b, t, e) implies {
            &&& post.mappings@.contains_key(mapping_node(t, e))
            &&& post.mappings@[mapping_node(t, e)].table == t
            &&& post.mappings@[mapping_node(t, e)].entry == e
        } by {
            assert(!(t == m.table && e == m.entry));
            assert(b.entry(t, e) == a.entry(t, e));
            assert(a.is_page(t));
            assert(a.record(t) == b.record(t));
            assert(frame_slot(a, t, e));
            assert(pre.mappings@.contains_key(mapping_node(t, e)));
            assert(mapping_node(t, e) != n);
        }
    }

    /// The hidden nodes after the step: r has gone. And every other capability node is still in its slot.
    pub proof fn lemma_revoke_hidden(pre: Self, post: Self, r: usize)
        requires
            Self::caps_frame(pre, post, r, r),
            post.table_pages.maps@.dom() == pre.table_pages.maps@.dom(),
            !post.list.nodes@[r as int].live,
            post.list.seq@[0] == pre.list.seq@[0],
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            capability_nodes_are_slots(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            assert(x != r);
            assert(pre.list.nodes@[x as int].live);
            assert(pre.tables.is_cap(&pre.list, x));
            Self::lemma_caps_frame(pre, post, r, r, x);
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != r);
            assert(pre.list.nodes@[x as int].live);
        }
    }

    /// What the step does to the view: only a node of c's run can leave it, and nothing is added.
    proof fn lemma_revoke_step(pre: Self, post: Self, root: usize, c: usize, r: usize)
        requires
            pre.wf(),
            post.list.wf(),
            pre.is_cap(c),
            pre.tables.owner@[page_of(c)].0 == root,
            post.tables.owner == pre.tables.owner,
            post.list.parent == pre.list.parent,
            !post.list.nodes@[r as int].live,
            has(pre.list.seq@, r),
            pre.list.d(r) > pre.list.d(c),
            pre.list.anc(r, (pre.list.d(r) - pre.list.d(c)) as nat) == c,
            forall|x: int| #![trigger post.list.nodes@[x]] 0 <= x < NODE_SPACE && x != r ==> {
                &&& post.list.nodes@[x].live == pre.list.nodes@[x].live
                &&& post.list.nodes@[x].kind == pre.list.nodes@[x].kind
            },
            forall|x: usize| x != r ==> #[trigger] post.tables.payload_of(x) == pre.tables.payload_of(x),
        ensures
            Self::caps_frame(pre, post, r, r),
            discharges(pre.view(), post.view(), root, Effect::Revoke { cap: c }),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && post.list.nodes@[x as int].live;
        let f = |x: NodeId| x;
        assert(Self::caps_frame(pre, post, r, r));
        assert forall|x: usize| #[trigger] post.is_cap(x) implies pre.is_cap(x) && x != r && x < NODE_SPACE && post.payload_of(x) == pre.payload_of(x) by {
            assert(x != r);
            Self::lemma_caps_frame(pre, post, r, r, x);
            pre.lemma_slot_bound(x);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1));
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
        assert forall|x: NodeId, q: Right| #[trigger] a.rights.contains((x, q)) implies b.rights.contains((f(x), q)) by {
            assert(post.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            post.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, f));
        assert(b.holds(root, c));
        assert forall|x: NodeId| #[trigger] State::removed(b, a, x) implies exists|k: nat| k > 0 && #[trigger] b.descends(c, x, k) by {
            if x != r {
                Self::lemma_caps_frame(pre, post, r, r, x);
            }
            assert(x == r);
            let k = (pre.list.d(r) - pre.list.d(c)) as nat;
            pre.lemma_anc_descends(r, k);
            assert(b.descends(c, r, k));
        }
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_revoke(b, a, root, c, live, f);
    }
}

} // verus!
