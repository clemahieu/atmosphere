// SPDX-License-Identifier: MIT

//! Revoking a capability, a bounded number of steps per kernel entry. A step finds a node of its run with
//! no children, undoes what that node's kind holds, and unlinks it, so revoke removes exactly the
//! capability's lineage, leaf first. See design/revoke-by-depth-first-list/.
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::position::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
use crate::capability::refs::*;
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::capability::view::*;
use crate::define::*;

/// How many steps a revoke does per kernel entry. No wait happens under the lock, so a revoke returns
/// and is called again. It is above the core count so the revoker outruns any number of deriving
/// threads, each core getting one entry per turn: reasoned in the design, not proven, since this
/// theorem is about safety.
pub const REVOKE_BUDGET: usize = 64;

/// The units of undoing a node by its kind: a mapping's stale note, the largest, or a device
/// binding's. Every other kind counts none. See design/one-lock-bounded-steps/.
pub const UNLINK_ARM_STEPS: usize = MAPPING_NOTE_STEPS;

/// The units of one revoke step, apart from the step's own: the walk to the run's leaf, the stale
/// note when the leaf is a table page's hidden node, and the leaf's arm. See
/// design/one-lock-bounded-steps/.
pub const REVOKE_STEP_STEPS: usize = MAX_DEPTH + CUT_NOTE_STEPS + UNLINK_ARM_STEPS;

/// revoke's bound in the step counter: REVOKE_BUDGET steps, each a unit of its own and its
/// REVOKE_STEP_STEPS.
pub const REVOKE_STEPS: usize = REVOKE_BUDGET * (REVOKE_STEP_STEPS + 1);

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
    /// records its unmap, clears its entry and drops its reference, and returns the entry's word as read
    /// in the step that cleared it; every other arm returns 0. A binding node, a thread's binding to its
    /// process, leaves the thread with no process and drops its reference on the process's block. A
    /// device binding node leaves its device bound to nothing and drops its reference on the space's
    /// block, recording the space's root stale at a new epoch.
    pub fn unlink_arm(&mut self, n: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: usize)
        requires
            old(self).wf(),
            n < NODE_SPACE,
            old(self).list.nodes@[n as int].live,
            n != old(self).list.seq@[0],
            old(self).list.nodes@[n as int].kind is Mapping ==> old(self).flush_epoch < usize::MAX,
            old(self).list.nodes@[n as int].kind is DeviceBinding ==> old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + UNLINK_ARM_STEPS,
            !(old(self).list.nodes@[n as int].kind is Mapping) && !(old(self).list.nodes@[n as int].kind is DeviceBinding)
                ==> final(steps).count == old(steps).count,
            final(self).tables.wf(&old(self).list),
            final(self).blocks.wf(),
            final(self).list == old(self).list,
            final(self).frames == old(self).frames,
            final(self).zeroing == old(self).zeroing,
            final(self).cores == old(self).cores,
            !(old(self).list.nodes@[n as int].kind is DeviceBinding) ==> final(self).devices == old(self).devices,
            final(self).devices.wf(),
            final(self).iommus.present == old(self).iommus.present,
            final(self).iommus.acked == old(self).iommus.acked,
            final(self).stale_epoch.wf(),
            final(self).tlb_wf(),
            mapped_wf(final(self).mapped@, final(self).mappings@),
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> {
                &&& final(self).tlb == old(self).tlb
                &&& final(self).iommus == old(self).iommus
                &&& final(self).mapped == old(self).mapped
            },
            !(old(self).list.nodes@[n as int].kind is Mapping) && !(old(self).list.nodes@[n as int].kind is DeviceBinding) ==> {
                &&& final(self).flush_epoch == old(self).flush_epoch
                &&& final(self).stale_epoch == old(self).stale_epoch
            },
            old(self).list.nodes@[n as int].kind is DeviceBinding ==> {
                &&& Self::device_unbound(*old(self), *final(self), n)
                &&& final(self).holders == old(self).holders
            },
            old(self).list.nodes@[n as int].kind is Mapping ==> Self::mapping_stale_noted(*old(self), *final(self), n),
            old(self).list.nodes@[n as int].kind is Mapping ==> Self::mapping_word(*old(self), n, ret),
            final(self).tables.owner == old(self).tables.owner,
            final(self).tables.roots@.dom() == old(self).tables.roots@.dom(),
            forall|x: usize| x != n ==> #[trigger] final(self).tables.payload_of(x) == old(self).tables.payload_of(x),
            final(self).tables == old(self).tables,
            final(self).table_pages.records == old(self).table_pages.records,
            final(self).table_pages.spare == old(self).table_pages.spare,
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> final(self).table_pages == old(self).table_pages,
            old(self).is_cap(n) && old(self).payload_of(n).kind is Frame ==> {
                let br = block_ref(&old(self).blocks, old(self).payload_of(n).base / PAGE_SZ);
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
                let br = BlockRef::Small(s / PAGE_SZ);
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
            !(old(self).is_cap(n) && old(self).payload_of(n).kind is Space) && !(old(self).list.nodes@[n as int].kind is DeviceBinding)
                ==> final(self).spaces == old(self).spaces,
            old(self).is_cap(n) && old(self).payload_of(n).kind is Thread ==> {
                let t = old(self).payload_of(n).base;
                let br = BlockRef::Small(t / PAGE_SZ);
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
                let br = BlockRef::Small(p / PAGE_SZ);
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
            final(self).spaces.registers == old(self).spaces.registers,
            final(self).spaces.kernel_root == old(self).spaces.kernel_root,
            !(old(self).list.nodes@[n as int].kind is DeviceBinding) ==> final(self).spaces.bound == old(self).spaces.bound,
            old(self).list.nodes@[n as int].kind is Mapping ==> Self::mapping_unlinked(*old(self), *final(self), n),
            !(old(self).list.nodes@[n as int].kind is Mapping) ==> {
                &&& Self::same_tree(*old(self), *final(self))
                &&& final(self).mappings == old(self).mappings
            },
            old(self).list.nodes@[n as int].kind is Hidden ==> {
                &&& blocks_refs_changed(&old(self).blocks, &final(self).blocks, BlockRef::Small(n / PAGE_SZ), 0, true)
                &&& final(self).holders == old(self).holders
            },
            !(old(self).is_cap(n) && (old(self).payload_of(n).kind is Frame || old(self).payload_of(n).kind is Space
                || old(self).payload_of(n).kind is Thread || old(self).payload_of(n).kind is Process))
                && !(old(self).list.nodes@[n as int].kind is Hidden) && !(old(self).list.nodes@[n as int].kind is Mapping)
                && !(old(self).list.nodes@[n as int].kind is Binding) && !(old(self).list.nodes@[n as int].kind is DeviceBinding) ==> {
                &&& final(self).blocks == old(self).blocks
                &&& final(self).holders == old(self).holders
            },
    {
        let ghost pre = *old(self);
        proof {
            self.list.lemma_live_valid(n);
        }
        let node = self.list.get(n);
        let mut word = 0;
        match node.kind {
            NodeKind::Hidden => {
                proof {
                    pre.lemma_hidden_block(n);
                }
                // The block's one reference was the hidden node's, so it is dead at once.
                drop_block_ref(&mut self.blocks, BlockRef::Small(n / PAGE_SZ));
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
                        let br = locate(&self.blocks, payload.base / PAGE_SZ);
                        drop_block_ref(&mut self.blocks, br);
                        self.holders = Ghost(pre.holders@.insert(br, pre.holders@[br].remove(n)));
                    },
                    CapKind::Space => {
                        proof {
                            pre.lemma_space_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                        self.spaces.holders = Ghost(pre.spaces.holders@.insert(payload.base, pre.spaces.holders@[payload.base].remove(n)));
                    },
                    CapKind::Thread => {
                        proof {
                            pre.lemma_thread_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                        self.threads.holders = Ghost(pre.threads.holders@.insert(payload.base, pre.threads.holders@[payload.base].remove(n)));
                    },
                    CapKind::Process => {
                        proof {
                            pre.lemma_process_cap(n);
                        }
                        drop_block_ref(&mut self.blocks, BlockRef::Small(payload.base / PAGE_SZ));
                        self.processes.holders = Ghost(pre.processes.holders@.insert(payload.base, pre.processes.holders@[payload.base].remove(n)));
                    },
                    _ => {},
                }
            },
            NodeKind::Mapping => { word = self.clear_mapping(n, Tracked(steps)); },
            NodeKind::Binding => { self.unbind(n); },
            NodeKind::DeviceBinding => { self.unbind_device(n, Tracked(steps)); },
        }
        proof {
            reveal(devices_wf);
            assert(self.devices.wf());
            if !(node.kind is Mapping) && !(node.kind is DeviceBinding) {
                Self::lemma_tlb_same(pre, *self);
            }
        }
        word
    }

    /// What a revoke of the capability at a position did when it was not refused, by a thread of the
    /// process whose table is at root: the position names a capability, which stays one, at most
    /// REVOKE_BUDGET nodes of its run went and no other node, no mapping appeared, the tables are as they
    /// were, no node changed its parent, the threads bound are those that were whose bindings are still
    /// live, the devices unbound are those whose binding nodes went, and the step discharges the
    /// revoke's effect for the caller, which commands the capability.
    pub open spec fn cap_revoking_at(pre: Self, post: Self, root: usize, at: Position) -> bool {
        let c = pre.cap_at(root, at)->0;
        &&& pre.cap_at(root, at) is Some
        &&& post.is_cap(c)
        &&& run_shrunk(pre.list, post.list, c)
        &&& post.tables == pre.tables
        &&& Self::mappings_shrunk(pre, post)
        &&& pre.list.seq@.len() - post.list.seq@.len() <= REVOKE_BUDGET
        &&& post.list.parent == pre.list.parent
        &&& discharges(pre.view(), post.view(), root, Effect::Revoke { cap: c })
        &&& bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).restrict(live_nodes(&post.list))
        &&& Self::devices_revoked(pre, post)
    }

    /// The devices after revoke steps from pre: a device whose binding node went is bound to nothing,
    /// unbound at some epoch, and every other device's record is as it was.
    pub open spec fn devices_revoked(pre: Self, post: Self) -> bool {
        &&& post.devices.count == pre.devices.count
        &&& post.devices.page == pre.devices.page
        &&& post.devices.holder == pre.devices.holder
        &&& forall|d: int| 0 <= d < pre.devices.count ==> {
            let n = pre.devices.page + 1 + d;
            let now = #[trigger] post.devices.records@[d];
            if pre.list.nodes@[n].live && pre.list.nodes@[n].kind is DeviceBinding && !post.list.nodes@[n].live {
                now == unbound_at(pre.devices.records@[d], now.unbound)
            } else {
                now == pre.devices.records@[d]
            }
        }
    }

    /// What a revoke of the capability at a position did when it finished: as cap_revoking_at says,
    /// and the capability has no child left.
    pub open spec fn cap_revoked_at(pre: Self, post: Self, root: usize, at: Position) -> bool {
        let c = pre.cap_at(root, at)->0;
        &&& Self::cap_revoking_at(pre, post, root, at)
        &&& post.list.childless(c)
        &&& forall|x: usize| !#[trigger] post.list.is_child(c, x)
    }

    /// Every mapping record after was one before, the same: a revoke takes records and adds none.
    pub open spec fn records_shrunk(pre: Self, post: Self) -> bool {
        forall|n: usize| #[trigger] post.mappings@.contains_key(n)
            ==> pre.mappings@.contains_key(n) && post.mappings@[n] == pre.mappings@[n]
    }

    /// Revokes the capability at a position, an index of the caller's table, at root, or of the table
    /// of a process the caller controls, live or dead, for at most REVOKE_BUDGET steps. The position
    /// comes from user space, so it can be refused. The capability's own slot can leave its table
    /// during the call, if the leaf holding it is in its run, and so can the capability the position
    /// goes through, so the steps name the capability's node and the authority is the caller's when
    /// the call began. Every page of a mapping it took is stale past the epoch it began at, so no core or
    /// IOMMU counts as having flushed it on an acknowledgement from before the call.
    pub fn revoke(&mut self, root: usize, at: Position, Tracked(steps): Tracked<&mut Steps>) -> (ret: RevokeStep)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(steps).count <= old(steps).count + REVOKE_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::mappings_shrunk(*old(self), *final(self)),
            ret is Refused == old(self).cap_at(root, at) is None,
            ret is Refused ==> *final(self) == *old(self),
            old(self).flush_epoch == usize::MAX ==> *final(self) == *old(self),
            ret is Exhausted ==> final(self).flush_epoch == usize::MAX,
            !(ret is Refused) ==> Self::cap_revoking_at(*old(self), *final(self), root, at),
            !(ret is Refused) ==> (ret is Done == final(self).list.childless(old(self).cap_at(root, at)->0)),
            ret is Done ==> Self::cap_revoked_at(*old(self), *final(self), root, at),
            Self::records_shrunk(*old(self), *final(self)),
            !(ret is Refused) ==> final(self).flush_epoch <= old(self).flush_epoch
                + (old(self).list.seq@.len() - final(self).list.seq@.len()),
            ret is Again ==> old(self).list.seq@.len() - final(self).list.seq@.len() == REVOKE_BUDGET,
            !(ret is Refused) ==> exists|gone: Seq<usize>|
                #[trigger] revoked_seq(old(self).list, final(self).list, old(self).cap_at(root, at)->0, gone),
            !(ret is Refused) ==> forall|n: usize, g: usize|
                old(self).mappings@.contains_key(n) && !final(self).mappings@.contains_key(n)
                && #[trigger] record_pages(old(self).mappings@[n]).contains(g)
                ==> final(self).stale_epoch.above(old(self).flush_epoch as int, g),
    {
        let ghost pre = *old(self);
        let c = match self.find_cap(root, at) {
            Some(found) => found.0,
            None => { return RevokeStep::Refused; },
        };
        let ghost holder = pre.tables.owner@[page_of(c)].0;
        proof {
            assert(pre.view().names.contains_key(c));
            assert(discharges(pre.view(), pre.view(), root, Effect::Revoke { cap: c }));
            lemma_bound_threads_live(&pre.list, &pre.tables);
        }
        let ghost start = steps.count;
        let ghost mut gone: Seq<usize> = Seq::empty();
        let mut taken = 0;
        while taken != REVOKE_BUDGET && self.flush_epoch != usize::MAX
            invariant
                taken <= REVOKE_BUDGET,
                self.flush_epoch <= pre.flush_epoch + taken,
                Self::records_shrunk(pre, *self),
                forall|x: int| 0 <= x < NODE_SPACE ==> #[trigger] self.list.nodes@[x].depth == pre.list.nodes@[x].depth,
                revoked_seq(pre.list, self.list, c, gone),
                start == old(steps).count,
                steps.count <= start + taken * (REVOKE_STEP_STEPS + 1),
                self.wf(),
                self.cores == pre.cores,
                pre == *old(self),
                pre.flush_epoch == usize::MAX ==> *self == pre,
                Self::mappings_shrunk(pre, *self),
                pre.cap_at(root, at) == Some(c),
                c < NODE_SPACE,
                self.is_cap(c),
                self.tables == pre.tables,
                run_shrunk(pre.list, self.list, c),
                self.list.parent == pre.list.parent,
                pre.list.seq@.len() - self.list.seq@.len() == taken,
                pre.tables.owner@[page_of(c)].0 == holder,
                pre.is_cap(c),
                discharges(pre.view(), self.view(), root, Effect::Revoke { cap: c }),
                bound_threads(&self.list, &self.tables) == bound_threads(&pre.list, &pre.tables).restrict(live_nodes(&self.list)),
                Self::devices_revoked(pre, *self),
                pre.flush_epoch <= self.flush_epoch,
                forall|n: usize, g: usize| pre.mappings@.contains_key(n) && !self.mappings@.contains_key(n)
                    && #[trigger] record_pages(pre.mappings@[n]).contains(g)
                    ==> self.stale_epoch.above(pre.flush_epoch as int, g) && (g as int) < NUM_PAGES,
            decreases REVOKE_BUDGET - taken,
        {
            let ghost mid = *self;
            proof {
                steps.step();
                assert((taken + 1) * (REVOKE_STEP_STEPS + 1) == taken * (REVOKE_STEP_STEPS + 1) + REVOKE_STEP_STEPS + 1) by (nonlinear_arith);
                assert((taken + 1) * (REVOKE_STEP_STEPS + 1) <= REVOKE_BUDGET * (REVOKE_STEP_STEPS + 1)) by (nonlinear_arith)
                    requires
                        taken < REVOKE_BUDGET,
                ;
            }
            if self.revoke_step(Ghost(holder), c, Tracked(steps)) {
                proof {
                    assert(self.view() == mid.view());
                }
                return RevokeStep::Done;
            }
            proof {
                lemma_revoke_steps_compose(pre.view(), mid.view(), self.view(), root, holder, c);
                assert(mid.list.nodes@.len() == NODE_SPACE) by {
                    reveal(Tree::store_wf);
                }
                let r = choose|r: usize| #[trigger] revoked_one(mid.list, self.list, c, r)
                    && mid.list.nodes@[r as int].live
                    && (mid.list.nodes@[r as int].kind is DeviceBinding ==> Self::device_unbound(mid, *self, r))
                    && (!(mid.list.nodes@[r as int].kind is DeviceBinding) ==> self.devices == mid.devices)
                    && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(mid, *self, r))
                    && (mid.list.nodes@[r as int].kind is Mapping ==> Self::mapping_stale_noted(mid, *self, r))
                    && (mid.hidden_table(r) ==> Self::table_unlinked(mid, *self, r))
                    && (mid.list.nodes@[r as int].kind is Binding ==> bound_threads(&self.list, &self.tables)
                        == bound_threads(&mid.list, &mid.tables).remove(r))
                    && (!(mid.list.nodes@[r as int].kind is Binding) ==> bound_threads(&self.list, &self.tables)
                        == bound_threads(&mid.list, &mid.tables));
                Self::lemma_revoke_bound_threads(bound_threads(&pre.list, &pre.tables), mid, *self, r);
                assert(mid.devices.wf()) by {
                    reveal(devices_wf);
                }
                Self::lemma_devices_revoked_step(pre, mid, *self, c, r);
                lemma_revoked_seq_step(pre.list, mid.list, self.list, c, r, gone);
                lemma_run_shrunk_step(pre.list, mid.list, self.list, c, r);
                gone = gone.push(r);
                // A record this step took is above the step's first epoch, so above the revoke's; one an
                // earlier step took stays above the revoke's first epoch, which is no later than this one's.
                assert forall|n: usize, g: usize| pre.mappings@.contains_key(n) && !self.mappings@.contains_key(n)
                    && #[trigger] record_pages(pre.mappings@[n]).contains(g)
                    implies self.stale_epoch.above(pre.flush_epoch as int, g) && (g as int) < NUM_PAGES by {
                    if mid.mappings@.contains_key(n) {
                        assert(mid.mappings@[n] == pre.mappings@[n]);
                        assert(record_pages(mid.mappings@[n]).contains(g));
                        assert(self.stale_epoch.above(mid.flush_epoch as int, g));
                    } else {
                        assert(mid.stale_epoch.above(pre.flush_epoch as int, g));
                    }
                }
            }
            taken = taken + 1;
        }
        proof {
            assert(taken * (REVOKE_STEP_STEPS + 1) <= REVOKE_BUDGET * (REVOKE_STEP_STEPS + 1)) by (nonlinear_arith)
                requires
                    taken <= REVOKE_BUDGET,
            ;
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
    pub fn revoke_step(&mut self, Ghost(root): Ghost<usize>, c: usize, Tracked(steps): Tracked<&mut Steps>) -> (done: bool)
        requires
            old(self).wf(),
            c < NODE_SPACE,
            old(self).is_cap(c),
            old(self).tables.owner@[page_of(c)].0 == root,
            old(self).flush_epoch < usize::MAX,
        ensures
            final(steps).count <= old(steps).count + REVOKE_STEP_STEPS,
            final(self).wf(),
            final(self).cores == old(self).cores,
            Self::mappings_shrunk(*old(self), *final(self)),
            final(self).is_cap(c),
            final(self).tables == old(self).tables,
            forall|x: int| 0 <= x < NODE_SPACE && #[trigger] final(self).list.nodes@[x].live
                ==> final(self).list.nodes@[x].kind == old(self).list.nodes@[x].kind,
            final(self).list.parent == old(self).list.parent,
            done == old(self).list.childless(c),
            done ==> *final(self) == *old(self),
            done ==> forall|x: usize| !#[trigger] old(self).list.is_child(c, x),
            !done ==> final(self).list.seq@.len() == old(self).list.seq@.len() - 1,
            !done ==> exists|r: usize| #[trigger] revoked_one(old(self).list, final(self).list, c, r)
                && old(self).list.nodes@[r as int].live
                && (old(self).list.nodes@[r as int].kind is DeviceBinding ==> Self::device_unbound(*old(self), *final(self), r))
                && (!(old(self).list.nodes@[r as int].kind is DeviceBinding) ==> final(self).devices == old(self).devices)
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
            final(self).flush_epoch <= old(self).flush_epoch + 1,
            old(self).flush_epoch <= final(self).flush_epoch,
            Self::records_shrunk(*old(self), *final(self)),
            forall|a: int, g: usize| a <= old(self).flush_epoch && g < NUM_PAGES && old(self).stale_epoch.above(a, g)
                ==> #[trigger] final(self).stale_epoch.above(a, g),
            forall|n: usize, g: usize| old(self).mappings@.contains_key(n) && !final(self).mappings@.contains_key(n)
                && #[trigger] record_pages(old(self).mappings@[n]).contains(g)
                ==> final(self).stale_epoch.above(old(self).flush_epoch as int, g) && (g as int) < NUM_PAGES,
    {
        let ghost pre = *old(self);
        proof {
            pre.lemma_no_change_discharges_revoke(root, c);
        }
        let r = match self.list.leaf_of_run(c, Tracked(&mut *steps)) {
            Some(found) => found,
            None => { return true; },
        };
        self.cut_hidden_table(r, Tracked(&mut *steps));
        let ghost cut = *self;
        self.unlink_arm(r, Tracked(steps));
        let ghost mid = *self;
        self.list.remove_leaf(r);
        proof {
            // A hidden table's cut records one unmap and its arm none; a mapping's arm records one.
            if pre.hidden_table(r) {
                assert(cut.flush_epoch == pre.flush_epoch + 1);
                assert(cut.mappings == pre.mappings);
                assert(!(cut.list.nodes@[r as int].kind is Mapping));
            }
            assert(mid.flush_epoch <= pre.flush_epoch + 1);
            assert(Self::records_shrunk(pre, mid));
            Self::lemma_revoke_step_wf(cut, mid, *self, root, c, r);
            if pre.hidden_table(r) {
                // The cut took walks from a device space at most, and the rest of the step none.
                Self::lemma_cut_sheds(pre, cut, r);
                assert(Self::same_tree(cut, mid));
                assert(self.view().shares == cut.view().shares);
                assert(self.devices == pre.devices);
                assert(self.view().binds == pre.view().binds);
                Self::lemma_revoke_step(pre, *self, root, c, r);
                Self::lemma_cut_recorded_same(pre, cut, *self, r);
                Self::lemma_cut_shrunk(pre, cut, r);
                Self::lemma_shrunk_compose(pre, cut, *self);
                assert(Self::table_unlinked(pre, *self, r));
            }
            assert(revoked_one(pre.list, self.list, c, r));
            // A device binding's arm unbinds its device, from a state the cut left alone; every other
            // step leaves the devices as they were.
            if pre.list.nodes@[r as int].kind is DeviceBinding {
                assert(cut == pre);
                assert(Self::device_unbound(pre, *self, r));
            } else {
                assert(self.devices == pre.devices);
            }
            // Each part of the step bumps the epoch or keeps it, and a word it writes is at the new epoch,
            // so a page above an acknowledgement no later than the step's first epoch stays above it.
            assert(pre.flush_epoch <= cut.flush_epoch);
            assert forall|a: int, g: usize| a <= pre.flush_epoch && g < NUM_PAGES && pre.stale_epoch.above(a, g)
                implies #[trigger] cut.stale_epoch.above(a, g) by {
                if pre.hidden_table(r) {
                    assert(pre.blocks.tracks(g as int));
                }
            }
            assert(cut.flush_epoch <= mid.flush_epoch);
            assert forall|a: int, g: usize| a <= cut.flush_epoch && g < NUM_PAGES && cut.stale_epoch.above(a, g)
                implies #[trigger] mid.stale_epoch.above(a, g) by {
            }
            assert(self.stale_epoch == mid.stale_epoch);
            assert(self.flush_epoch == mid.flush_epoch);
            assert(self.mappings == mid.mappings);
            // Only a mapping's own arm takes a record, at an epoch past the step's first.
            assert forall|n: usize, g: usize| pre.mappings@.contains_key(n) && !self.mappings@.contains_key(n)
                && #[trigger] record_pages(pre.mappings@[n]).contains(g)
                implies self.stale_epoch.above(pre.flush_epoch as int, g) && (g as int) < NUM_PAGES by {
                if pre.list.nodes@[r as int].kind is Mapping {
                    assert(cut == pre);
                    assert(mid.mappings@ == pre.mappings@.remove(r));
                    assert(n == r);
                    assert(mid.stale_epoch.written(mid.flush_epoch, g));
                } else {
                    assert(cut.mappings == pre.mappings);
                    assert(mid.mappings == cut.mappings);
                }
            }
        }
        false
    }

    /// The state after the leaf r of c's run has its arm unlinked and its node removed: well formed,
    /// with r's capability and its mapping gone and every other capability as it was.
    pub proof fn lemma_revoke_step_wf(pre: Self, mid: Self, post: Self, root: usize, c: usize, r: usize)
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
                let br = block_ref(&pre.blocks, pre.payload_of(r).base / PAGE_SZ);
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
                let br = BlockRef::Small(s / PAGE_SZ);
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
            !(pre.is_cap(r) && pre.payload_of(r).kind is Space) && !(pre.list.nodes@[r as int].kind is DeviceBinding)
                ==> mid.spaces == pre.spaces,
            pre.is_cap(r) && pre.payload_of(r).kind is Thread ==> {
                let t = pre.payload_of(r).base;
                let br = BlockRef::Small(t / PAGE_SZ);
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
                let br = BlockRef::Small(p / PAGE_SZ);
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
            mid.spaces.registers == pre.spaces.registers,
            mid.spaces.kernel_root == pre.spaces.kernel_root,
            !(pre.list.nodes@[r as int].kind is DeviceBinding) ==> mid.spaces.bound == pre.spaces.bound,
            !(pre.list.nodes@[r as int].kind is DeviceBinding) ==> mid.devices == pre.devices,
            mid.devices.wf(),
            mid.iommus.present == pre.iommus.present,
            mid.iommus.acked == pre.iommus.acked,
            pre.list.nodes@[r as int].kind is DeviceBinding ==> {
                &&& Self::device_unbound(pre, mid, r)
                &&& mid.holders == pre.holders
            },
            pre.list.nodes@[r as int].kind is Mapping ==> Self::mapping_unlinked(pre, mid, r),
            !(pre.list.nodes@[r as int].kind is Mapping) ==> {
                &&& Self::same_tree(pre, mid)
                &&& mid.mappings == pre.mappings
            },
            pre.list.nodes@[r as int].kind is Hidden ==> {
                &&& blocks_refs_changed(&pre.blocks, &mid.blocks, BlockRef::Small(r / PAGE_SZ), 0, true)
                &&& mid.holders == pre.holders
            },
            !(pre.is_cap(r) && (pre.payload_of(r).kind is Frame || pre.payload_of(r).kind is Space
                || pre.payload_of(r).kind is Thread || pre.payload_of(r).kind is Process))
                && !(pre.list.nodes@[r as int].kind is Hidden) && !(pre.list.nodes@[r as int].kind is Mapping)
                && !(pre.list.nodes@[r as int].kind is Binding) && !(pre.list.nodes@[r as int].kind is DeviceBinding) ==> {
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
        assert(post.view().shares.subset_of(pre.view().shares)) by {
            assert(post.view().shares == mid.view().shares);
            if pre.list.nodes@[r as int].kind is Mapping {
                Self::lemma_unlinked_shrunk(pre, mid, r);
                Self::lemma_shrunk_sheds(pre, mid);
            } else {
                assert(Self::same_tree(pre, mid));
            }
        }
        // Only the device unbound leaves the binds, and every other record is as it was.
        assert forall|o: ObjectId| #[trigger] post.view().binds.contains_key(o) implies {
            &&& pre.view().binds.contains_key(o)
            &&& pre.view().binds[o] == post.view().binds[o]
        } by {
            if pre.list.nodes@[r as int].kind is DeviceBinding {
                let d = binding_device(&pre.devices, r);
                if device_of(o) != d {
                    assert(post.devices.records@[device_of(o)] == pre.devices.records@[device_of(o)]);
                }
            }
        }
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
            Self::lemma_device_bindings_caps_frame(pre, post, r, r);
        } else if pre.list.nodes@[r as int].kind is DeviceBinding {
            Self::lemma_revoke_device_binding_holders(pre, post, r);
            Self::lemma_same_tree_shrunk(pre, post);
            // The device unbound is bound to nothing, and every other record is as it was.
            assert forall|e: int| 0 <= e < post.devices.count && (#[trigger] post.devices.records@[e]).space is Some implies {
                &&& post.iommus.present@[post.devices.records@[e].iommu as int]
                &&& post.devices.records@[e].unbound <= post.iommus.acked@[post.devices.records@[e].iommu as int]
            } by {
                assert(post.devices.records@[e] == pre.devices.records@[e]);
            }
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

    /// A revoke step that took r from mid keeps the devices as devices_revoked says from the state the
    /// revoke began in: r's device, if r is a device binding, is the one device it unbinds.
    proof fn lemma_devices_revoked_step(pre: Self, mid: Self, post: Self, c: usize, r: usize)
        requires
            mid.devices.wf(),
            mid.list.nodes@.len() == NODE_SPACE,
            Self::devices_revoked(pre, mid),
            run_shrunk(pre.list, mid.list, c),
            revoked_one(mid.list, post.list, c, r),
            mid.list.nodes@[r as int].live,
            mid.list.nodes@[r as int].kind is DeviceBinding ==> Self::device_unbound(mid, post, r),
            !(mid.list.nodes@[r as int].kind is DeviceBinding) ==> post.devices == mid.devices,
        ensures
            Self::devices_revoked(pre, post),
    {
        assert forall|d: int| 0 <= d < pre.devices.count implies {
            let n = pre.devices.page + 1 + d;
            let now = #[trigger] post.devices.records@[d];
            if pre.list.nodes@[n].live && pre.list.nodes@[n].kind is DeviceBinding && !post.list.nodes@[n].live {
                now == unbound_at(pre.devices.records@[d], now.unbound)
            } else {
                now == pre.devices.records@[d]
            }
        } by {
            let n = pre.devices.page + 1 + d;
            assert(0 <= n < NODE_SPACE);
            assert(mid.list.nodes@[n].live ==> pre.list.nodes@[n].live && mid.list.nodes@[n].kind == pre.list.nodes@[n].kind);
            if n != r {
                assert(post.list.nodes@[n].live == mid.list.nodes@[n].live);
            }
            assert(mid.devices.records@[d] == mid.devices.records@[d]);
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
            blocks_refs_changed(&pre.blocks, &post.blocks, BlockRef::Small(n / PAGE_SZ), 0, true),
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
        let br = BlockRef::Small(n / PAGE_SZ);
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
        assert(!(pre.blocks.pages@[(n / PAGE_SZ) as int].object is Space));
        assert(!(pre.blocks.pages@[(n / PAGE_SZ) as int].object is Thread));
        assert(!(pre.blocks.pages@[(n / PAGE_SZ) as int].object is Process));
        lemma_spaces_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, br, 0, true);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, 0, true);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, 0, true);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, n / PAGE_SZ, 0, true);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, n / PAGE_SZ, 0, true);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, n / PAGE_SZ, 0, true);
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
            lemma_leaf_blocks_other_changed(&pre.list, &post.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, n / PAGE_SZ, 0, true);
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
        let br = BlockRef::Small(p / PAGE_SZ);
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
                assert(pre.blocks.pages@[(p / PAGE_SZ) as int].object is Frame);
            }
        }
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, p / PAGE_SZ, refs, dead);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, p / PAGE_SZ, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, refs, dead);
        // Node n is a thread's base, so no leaf's and no table page's.
        assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        assert(pre.blocks.pages@[(t / PAGE_SZ) as int].object is Thread);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
            assert(pre.blocks.pages@[(l / PAGE_SZ) as int].object is TableLeaf);
            assert(l != n);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, p / PAGE_SZ, refs, dead);
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

    /// The invariant's parts after device binding node n goes with its device's binding and its
    /// reference on the space's block: no capability, mapping, frame, thread or process changed, only that
    /// block's count did, and the device left its space's bound set.
    pub proof fn lemma_revoke_device_binding_holders(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is DeviceBinding,
            !post.list.nodes@[n as int].live,
            post.zeroing == pre.zeroing,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            post.list.parent@ == pre.list.parent@,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.mappings == pre.mappings,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.holders == pre.holders,
            Self::device_unbound(pre, post, n),
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
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        let d = binding_device(&pre.devices, n);
        let s = pre.devices.records@[d].space->Some_0;
        let br = BlockRef::Small(s / PAGE_SZ);
        let refs = (block_refs(&pre.blocks, br) - 1) as usize;
        let dead = block_dead(&pre.blocks, br) || block_refs(&pre.blocks, br) == 1;
        let page = pre.devices.page;
        Self::lemma_binding_parents_caps_frame(pre, post, n, n);
        pre.lemma_bound_is_space(s, d as usize);
        assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        assert(pre.blocks.pages@[(s / PAGE_SZ) as int].object is Space);
        // Node n is a slot of the device page past its first, so no leaf's and no table page's node.
        assert((n as int) % (PAGE_SZ as int) != 0) by {
            reveal(devices_wf);
            assert(pre.devices.wf());
            assert(n == page + (1 + d));
            vstd::arithmetic::div_mod::lemma_add_mod_noop(page as int, 1 + d, PAGE_SZ as int);
            vstd::arithmetic::div_mod::lemma_small_mod((1 + d) as nat, PAGE_SZ as nat);
        }
        assert forall|x: usize| x != n implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_caps_frame(pre, post, n, n, x);
        }
        assert(!pre.is_cap(n));
        assert(!post.is_cap(n));
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x) by {
            if x != n {
                Self::lemma_caps_frame(pre, post, n, n, x);
            }
        }
        assert(same_mapping_nodes(&pre.list, &post.list));
        assert(same_frames(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_spaces(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_threads(&pre.list, &pre.tables, &post.list, &post.tables));
        assert(same_processes(&pre.list, &pre.tables, &post.list, &post.tables));
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, &pre.blocks, &pre.zeroing, pre.holders@);
        assert(!pre.holders@.contains_key(br)) by {
            if pre.holders@.contains_key(br) {
                assert(pre.blocks.pages@[(s / PAGE_SZ) as int].object is Frame);
            }
        }
        lemma_holders_unkeyed_small_changed(&post.list, &post.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, s / PAGE_SZ, refs, dead);
        lemma_zeroing_typed_small_changed(&pre.zeroing, &pre.blocks, &post.blocks, s / PAGE_SZ, refs, dead);
        lemma_list_pages_used_same_kinds(&pre.list, &pre.blocks, &post.blocks);
        assert(objects_wf(&post.tables, &pre.blocks, pre.holders@));
        lemma_objects_unframed_block_changed(&post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
            assert(l != n);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, &pre.blocks));
        lemma_leaf_blocks_other_changed(&pre.list, &post.list, &post.tables, &pre.blocks, &post.blocks, pre.holders@, s / PAGE_SZ, refs, dead);
        assert forall|u: usize| #[trigger] pre.table_pages.maps@.contains_key(u) implies {
            &&& post.list.nodes@[u as int].live == pre.list.nodes@[u as int].live
            &&& post.list.nodes@[u as int].kind == pre.list.nodes@[u as int].kind
        } by {
            pre.lemma_table_page_valid(u);
            assert(u != n);
        }
        lemma_table_pages_refs_changed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, br, refs, dead);
        Self::lemma_spaces_bound_dropped(pre, post, s, d as usize);
        lemma_threads_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, br, refs, dead);
        lemma_processes_refs_changed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, br, refs, dead);
        assert forall|m: usize| #[trigger] pre.mappings@.contains_key(m) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[m].frame, m,
        ) by {
            pre.lemma_mapping_node(m);
            let c = pre.list.parent@[m];
            assert(c != n);
            Self::lemma_caps_frame(pre, post, n, n, c);
        }
        Self::lemma_mappings_same_tree(pre, post);
        assert forall|x: usize| x < NODE_SPACE implies
            ((#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is Binding)
                == (pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is Binding) by {
            if x != n {
                assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
                assert(post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind);
            }
        }
        lemma_bindings_same(&pre.list, &post.list, &pre.threads, &pre.processes);
        Self::lemma_revoke_device_bindings(pre, post, n);
    }

    /// The device bindings after device binding node n goes: its device is bound to nothing and left its
    /// space's bound set, and every other device binding node, its parent and its device are as they were.
    proof fn lemma_revoke_device_bindings(pre: Self, post: Self, n: usize)
        requires
            Self::caps_frame(pre, post, n, n),
            n < NODE_SPACE,
            pre.list.nodes@[n as int].live,
            pre.list.nodes@[n as int].kind is DeviceBinding,
            !post.list.nodes@[n as int].live,
            post.list.parent@ == pre.list.parent@,
            Self::device_unbound(pre, post, n),
        ensures
            device_bindings_wf(&post.list, &post.tables, post.spaces.bound@, &post.devices),
    {
        reveal(device_bindings_wf);
        reveal(devices_wf);
        assert(pre.devices.wf());
        let d = binding_device(&pre.devices, n);
        assert(0 <= d < pre.devices.count);
        assert(n == binding_node(&pre.devices, d));
        let s = pre.devices.records@[d].space->Some_0;
        let ra = pre.devices.records@;
        let rb = post.devices.records@;
        let ba = pre.spaces.bound@;
        let bb = post.spaces.bound@;
        assert(rb[d].space is None);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live && post.list.nodes@[x as int].kind is DeviceBinding implies {
            let e = binding_device(&post.devices, x);
            &&& 0 <= e < post.devices.count
            &&& rb[e].space is Some
            &&& device_binding_parent(&post.list, &post.tables, x, rb[e].space->Some_0)
        } by {
            assert(x != n);
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding);
            let e = binding_device(&pre.devices, x);
            assert(e != d);
            assert(rb[e] == ra[e]);
            let q = pre.list.parent@[x];
            assert(device_binding_parent(&pre.list, &pre.tables, x, ra[e].space->Some_0));
            assert(q != n);
            Self::lemma_caps_frame(pre, post, n, n, q);
        }
        assert forall|e: int| 0 <= e < post.devices.count && (#[trigger] rb[e]).space is Some implies {
            let x = binding_node(&post.devices, e);
            let t = rb[e].space->Some_0;
            &&& x < NODE_SPACE
            &&& post.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind is DeviceBinding
            &&& bb.contains_key(t)
            &&& bb[t].contains(e as usize)
        } by {
            assert(e != d);
            assert(rb[e] == ra[e]);
            let x = binding_node(&pre.devices, e);
            let t = ra[e].space->Some_0;
            assert(pre.list.nodes@[x as int].live && pre.list.nodes@[x as int].kind is DeviceBinding);
            assert(x == pre.devices.page + 1 + e);
            assert(x != n);
            assert(ba[t].contains(e as usize));
        }
        assert forall|t: usize, e: usize| bb.contains_key(t) && #[trigger] bb[t].contains(e)
            implies e < post.devices.count && rb[e as int].space == Some(t) by {
            if t == s {
                assert(ba[s].contains(e));
                assert(e != d);
            } else {
                assert(ba[t].contains(e));
            }
            assert(ra[e as int].space == Some(t));
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
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && post.blocks.tracks_addr(p) implies {
            &&& !(post.blocks.pages@[(p / PAGE_SZ) as int].kind is Free)
            &&& post.blocks.pages@[(p / PAGE_SZ) as int].kind is Member
                ==> post.blocks.pages@[post.blocks.pages@[(p / PAGE_SZ) as int].base as int].object is TablePage
                    || post.blocks.pages@[post.blocks.pages@[(p / PAGE_SZ) as int].base as int].object is Space
            &&& !(post.blocks.pages@[(p / PAGE_SZ) as int].object is Frame)
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
        assert forall|i: usize| #![trigger post.table_pages.maps@[m.table].value()[i]] i < ENTRIES && i != m.entry
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
            post.view().shares.subset_of(pre.view().shares),
            binds_within(post.view(), pre.view()),
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
