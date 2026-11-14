// SPDX-License-Identifier: MIT

//! The witness that a holder of a core can take back the time it handed on: from the state boot
//! leaves, revoking a core capability leaves the thread placed below it Inactive and placed nowhere.
//! It is a module of its own, with the list lemmas it needs, so that the witness module's shared
//! solver context, in which several witnesses verify close to the solver's budget, does not grow with
//! it. Only Verus compiles this module, so no image contains it. See design/cpu-time-as-capability/.

use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::cpu::*;
use crate::capability::decompose::*;
use crate::capability::delete::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::device_space::{device_path, device_range_bytes, DeviceRange};
use crate::capability::guest_space::{guest_path, guest_range_bytes, GuestPhysRange};
use crate::capability::device::{
    binding_device, binding_node, bound_record, device_of, device_payload, lemma_device_object, devices_wf, DeviceInfo, IOMMU_DEVICES, MAX_DEVICES,
};
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::operation::Outcome;
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
use crate::arch::{partial_frame, saved_frame, user_frame, user_rip, FrameKind, Registers};
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::capability::witness::*;
use crate::define::*;

/// The index of the root's table a core capability the root derives from its own goes in, when it
/// hands a core on and takes it back: slot 3 of root entry 2.
pub const WITNESS_CORE_SLOT: usize = 259;

/// The index of the root's table a core capability derived from the one at WITNESS_CORE_SLOT goes in:
/// slot 4 of root entry 2.
pub const WITNESS_SUBCORE_SLOT: usize = 260;

/// After a step that put node x in the list under q and left every other node live or not as it was,
/// a node's child is x or one it had before.
proof fn lemma_children_after_add(pre: Tree, post: Tree, x: usize, q: usize)
    requires
        pre.wf(),
        post.wf(),
        post.parent@ == pre.parent@.insert(x, q),
        post.seq@[0] == pre.seq@[0],
        forall|y: int| #![trigger post.nodes@[y]] 0 <= y < NODE_SPACE && y != x ==> post.nodes@[y].live == pre.nodes@[y].live,
    ensures
        forall|c: usize, i: usize| #[trigger] post.is_child(c, i) ==> i == x || pre.is_child(c, i),
{
    assert forall|c: usize, i: usize| #[trigger] post.is_child(c, i) implies i == x || pre.is_child(c, i) by {
        if i != x {
            lemma_listed_live(post, i);
            assert(pre.nodes@[i as int].live);
            assert(has(pre.seq@, i));
            lemma_has(pre.seq@, i);
        }
    }
}

/// Below c, a live node is m or p, when c's only child is m, m's only child is p, and p has none.
proof fn lemma_below_two(t: Tree, c: usize, m: usize, p: usize, x: usize)
    requires
        t.wf(),
        x < NODE_SPACE,
        t.nodes@[x as int].live,
        below(t, c, x),
        forall|y: usize| #[trigger] t.is_child(c, y) ==> y == m,
        forall|y: usize| #[trigger] t.is_child(m, y) ==> y == p,
        forall|y: usize| !#[trigger] t.is_child(p, y),
    ensures
        x == m || x == p,
    decreases t.d(x) - t.d(c),
{
    let s = t.seq@;
    assert(has(s, x));
    lemma_has(s, x);
    let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
    assert(k != 0);
    assert(t.parent@.contains_key(s[k]));
    let q = t.parent@[x];
    t.lemma_parent_live(x);
    let n = (t.d(x) - t.d(c)) as nat;
    assert(t.anc(x, n) == t.anc(q, (n - 1) as nat));
    assert(t.is_child(q, x));
    if n > 1 {
        assert(t.d(q) == t.d(x) - 1);
        assert(below(t, c, q));
        lemma_below_two(t, c, m, p, q);
    } else {
        assert(t.anc(q, 0) == q);
    }
}

impl CapKernel {
    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: the root retypes a leaf
    /// into root entry 2 of its own table, a process at `base` into slot 1 of that leaf and a thread at
    /// `base + 10 * PAGE_SZ` into slot 2 bound to that process, as witness_root_starts_placed_thread
    /// does. It derives from its capability for core 0 one at priority 7 into slot 3 of that leaf, and
    /// from that one, one at priority 5 into slot 4, places the thread through the second at priority 3
    /// and starts it, then revokes the first. The revoke finishes: it took the second capability and the
    /// placement under it, and the thread, Runnable before, is Inactive and placed nowhere. The use is a
    /// holder of a core taking back the time it handed on, from every thread placed below it.
    /// design/witness-per-way-an-operation-succeeds/, design/cpu-time-as-capability/.
    #[verifier::spinoff_prover]
    pub fn witness_revoked_core_stops_its_thread(
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
        kernel_root: Ghost<usize>,
        base: usize,
    ) -> (ret: (bool, bool, RevokeStep))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret.0,
            ret.1,
            ret.2 is Done,
            ({
                let thread = (base + 10 * PAGE_SZ) as usize;
                let core = (base + PROCESS_BYTES + 3) as usize;
                &&& final(self).wf()
                &&& final(self).is_cap(core)
                &&& final(self).payload_of(core) == core_payload(0, 7)
                &&& forall|x: usize| !#[trigger] final(self).list.is_child(core, x)
                &&& final(self).threads.records@.contains_key(thread)
                &&& final(self).threads.records@[thread].value().state is Inactive
                &&& final(self).threads.records@[thread].value().placement is None
                &&& !final(self).threads.records@[thread].value().pending_stop
                &&& !final(self).list.nodes@[placement_node(thread) as int].live
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        let ghost core_cap = (leaf@ + ROOT_CORE_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
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
            assert(s0.slot_holds(process, ROOT_CORE_SLOT, core_cap, core_payload(0, MAX_PRIORITY)));
            assert(s0.list.nodes@[core_cap as int].depth == 1);
            assert(s0.tables.has_slot(&s0.list, process, ROOT_CORE_SLOT));
            assert(s0.is_cap(core_cap));
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
        }
        let b2 = base + PROCESS_BYTES;
        let bt = b2 + 2 * PAGE_SZ;
        proof {
            assert(block_bytes(3) == PROCESS_BYTES);
            assert(block_bytes(1) == 2 * PAGE_SZ);
            assert(base % PROCESS_BYTES == 0);
            assert(b2 % PROCESS_BYTES == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            assert(b2 / PAGE_SZ == base / PAGE_SZ + 8);
            assert(bt / PAGE_SZ == b2 / PAGE_SZ + 2);
            assert(!s0.blocks.covered((base / PAGE_SZ) as int));
            assert(!s0.blocks.covered((b2 / PAGE_SZ) as int));
            assert(!s0.blocks.covered(b2 / PAGE_SZ + 2));
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
            assert(s1.tables.has_slot(&s1.list, process, ROOT_CORE_SLOT));
            assert(s1.tables.node_of(process, ROOT_CORE_SLOT) == core_cap);
            assert(s1.is_cap(core_cap) && s1.payload_of(core_cap) == core_payload(0, MAX_PRIORITY) && s1.list.nodes@[core_cap as int].depth == 1);
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_THREAD_SLOT) && index_entry(WITNESS_THREAD_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_PROCESS_SLOT) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_THREAD_SLOT) as int].live);
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b2 + 1);
            assert(s1.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(index_ok(WITNESS_CORE_SLOT) && index_entry(WITNESS_CORE_SLOT) == 2);
            assert(index_ok(WITNESS_SUBCORE_SLOT) && index_entry(WITNESS_SUBCORE_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_CORE_SLOT));
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_SUBCORE_SLOT));
            assert(s1.tables.node_of(process, WITNESS_CORE_SLOT) == b2 + 3);
            assert(s1.tables.node_of(process, WITNESS_SUBCORE_SLOT) == b2 + 4);
            assert(!s1.list.nodes@[(b2 + 3) as int].live);
            assert(!s1.list.nodes@[(b2 + 4) as int].live);
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
            assert(s2.processes.records@.contains_key(base));
            assert(!s2.processes.records@[base].value().dead);
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.payload_of(np).rights & right_bit(Right::Control) != 0);
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.is_cap(np));
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.is_cap(u));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.tables.has_slot(&s1.list, process, ROOT_CORE_SLOT));
            assert(s1.is_cap(core_cap));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_CORE_SLOT));
            assert(s2.tables.node_of(process, ROOT_CORE_SLOT) == core_cap);
            assert(s2.is_cap(core_cap) && s2.payload_of(core_cap) == core_payload(0, MAX_PRIORITY) && s2.list.nodes@[core_cap as int].depth == 1);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(!s2.list.nodes@[(b2 + 2) as int].live);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_CORE_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_SUBCORE_SLOT));
            assert(s2.tables.node_of(process, WITNESS_CORE_SLOT) == b2 + 3);
            assert(s2.tables.node_of(process, WITNESS_SUBCORE_SLOT) == b2 + 4);
            assert(!s2.list.nodes@[(b2 + 3) as int].live);
            assert(!s2.list.nodes@[(b2 + 4) as int].live);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.processes.records@.contains_key(process));
            assert(s2.root_live(process));
            assert(s2.tables.roots@.contains_key(process));
            assert forall|i: int| b2 / PAGE_SZ + 2 <= i < b2 / PAGE_SZ + 8 implies #[trigger] s2.blocks.pages@[i].kind is Free by {
                assert(s1.blocks.tracks(i));
                assert(s1.blocks.pages@[i].kind is Free);
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
        let ghost nt = (b2 + 2) as usize;
        proof {
            assert(ok3);
            assert(Self::retype_keeps(s2, s3, nt, (bt / PAGE_SZ) as int, 1, None));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_CORE_SLOT));
            assert(s2.is_cap(core_cap));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_CORE_SLOT));
            assert(s3.tables.node_of(process, ROOT_CORE_SLOT) == core_cap);
            assert(s3.is_cap(core_cap) && s3.payload_of(core_cap) == core_payload(0, MAX_PRIORITY) && s3.list.nodes@[core_cap as int].depth == 1);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_THREAD_SLOT));
            assert(s3.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_CORE_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_SUBCORE_SLOT));
            assert(s3.tables.node_of(process, WITNESS_CORE_SLOT) == b2 + 3);
            assert(s3.tables.node_of(process, WITNESS_SUBCORE_SLOT) == b2 + 4);
            assert(!s3.list.nodes@[(b2 + 3) as int].live);
            assert(!s3.list.nodes@[(b2 + 4) as int].live);
            assert(s3.is_cap(nt) && s3.payload_of(nt) == thread_of(bt));
            assert(s3.payload_of(nt).rights & right_bit(Right::Control) != 0);
            assert(s2.processes.records@.contains_key(process));
            assert(s3.processes.records@.contains_key(process));
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s3.processes.records@.contains_key(base));
            assert(!s3.processes.records@[base].value().dead);
            assert(!s3.cap_dead(nt));
            assert(s3.can_control(process, WITNESS_THREAD_SLOT));
            assert(1usize < MAX_DEPTH) by (compute_only);
            assert(s3.holds_core(process, ROOT_CORE_SLOT, 0));
            assert(s3.can_place(process, WITNESS_THREAD_SLOT, ROOT_CORE_SLOT, 0));
        }


        // The root hands on core 0 at priority 7, and that holder hands it on at priority 5.
        let ghost nd = (b2 + 3) as usize;
        let ghost nm = (b2 + 4) as usize;
        let ghost pn = placement_node(bt);
        let to1 = Position { through: None, index: WITNESS_CORE_SLOT };
        proof {
            assert(s3.list.wf()) by {
                reveal(CapKernel::wf);
            }
            assert(s3.can_place(process, WITNESS_THREAD_SLOT, ROOT_CORE_SLOT, 0));
            assert(s3.threads.records@.contains_key(bt));
            assert(s3.threads.records@[bt].value().state is Inactive);
            assert(s3.threads.records@[bt].value().placement is None);
            assert(s3.flush_epoch == 0);
            assert(CORE_RIGHTS & !CORE_RIGHTS == 0) by (compute_only);
            s3.lemma_console_power_derive(process, ROOT_CORE_SLOT, process, WITNESS_CORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 7);
            assert(core_object(0) == CORE_OBJECTS);
            assert(s3.can_derive_between(process, ROOT_CORE_SLOT, process, WITNESS_CORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 7));
            assert(s3.table_at(process, None) == Some(process));
            assert(s3.can_derive_at(process, ROOT_CORE_SLOT, to1, CORE_RIGHTS, CORE_OBJECTS, 7));
        }
        let d1 = self.derive(process, ROOT_CORE_SLOT, to1, CORE_RIGHTS, CORE_OBJECTS, 7);
        let ghost s4 = *self;
        proof {
            assert(d1);
            assert(Self::cap_derived_between(s3, s4, process, ROOT_CORE_SLOT, process, WITNESS_CORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 7));
            assert(Self::derive_step(s3, s4, nd));
            assert(s4.payload_of(nd) == child_of(core_payload(0, MAX_PRIORITY), CORE_RIGHTS, CORE_OBJECTS, 7));
            assert(s4.payload_of(nd) == core_payload(0, 7));
            assert(s4.list.nodes@[nd as int].depth == 2);
            assert(!tracked_kind(s3.payload_of(core_cap).kind));
            assert(s4.threads == s3.threads && s4.processes == s3.processes && s4.blocks == s3.blocks);
            assert(s4.list.wf()) by {
                reveal(CapKernel::wf);
            }
            // nd is new, so it has no child, and every other node's children are as they were.
            lemma_children_after_add(s3.list, s4.list, nd, core_cap);
            assert forall|y: usize| !#[trigger] s4.list.is_child(nd, y) by {
                s3.list.lemma_dead_childless(nd, y);
            }
            assert(b2 != nd && b2 != nm);
            assert(s4.list.nodes@[b2 as int].live == s3.list.nodes@[b2 as int].live);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_CORE_SLOT));
            assert(s4.tables.node_of(process, WITNESS_CORE_SLOT) == nd);
            assert(s4.is_cap(nd));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_SUBCORE_SLOT));
            assert(s4.tables.node_of(process, WITNESS_SUBCORE_SLOT) == nm);
            assert(!s4.list.nodes@[nm as int].live);
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_THREAD_SLOT));
            assert(s4.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            Self::lemma_caps_frame(s3, s4, nd, nd, nt);
            assert(s4.is_cap(nt) && s4.payload_of(nt) == thread_of(bt));
            assert(s4.root_live(process));
            assert(s4.flush_epoch == 0);
            s4.lemma_console_power_derive(process, WITNESS_CORE_SLOT, process, WITNESS_SUBCORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 5);
            assert(2usize < MAX_DEPTH) by (compute_only);
            assert(s4.can_derive_between(process, WITNESS_CORE_SLOT, process, WITNESS_SUBCORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 5));
            assert(s4.table_at(process, None) == Some(process));
        }
        let to2 = Position { through: None, index: WITNESS_SUBCORE_SLOT };
        proof {
            assert(s4.can_derive_at(process, WITNESS_CORE_SLOT, to2, CORE_RIGHTS, CORE_OBJECTS, 5));
        }
        let d2 = self.derive(process, WITNESS_CORE_SLOT, to2, CORE_RIGHTS, CORE_OBJECTS, 5);
        let ghost s5 = *self;
        proof {
            assert(d2);
            assert(Self::cap_derived_between(s4, s5, process, WITNESS_CORE_SLOT, process, WITNESS_SUBCORE_SLOT, CORE_RIGHTS, CORE_OBJECTS, 5));
            assert(Self::derive_step(s4, s5, nm));
            assert(s5.payload_of(nm) == child_of(core_payload(0, 7), CORE_RIGHTS, CORE_OBJECTS, 5));
            assert(s5.payload_of(nm) == core_payload(0, 5));
            assert(s5.list.nodes@[nm as int].depth == 3);
            assert(!tracked_kind(s4.payload_of(nd).kind));
            assert(s5.threads == s4.threads && s5.processes == s4.processes && s5.blocks == s4.blocks);
            assert(s5.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_children_after_add(s4.list, s5.list, nm, nd);
            assert forall|y: usize| #[trigger] s5.list.is_child(nd, y) implies y == nm by {
                assert(!s4.list.is_child(nd, y));
            }
            assert forall|y: usize| !#[trigger] s5.list.is_child(nm, y) by {
                s4.list.lemma_dead_childless(nm, y);
            }
            assert(s5.list.nodes@[b2 as int].live == s4.list.nodes@[b2 as int].live);
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_CORE_SLOT));
            Self::lemma_caps_frame(s4, s5, nm, nm, nd);
            assert(s5.is_cap(nd) && s5.payload_of(nd) == core_payload(0, 7));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_SUBCORE_SLOT));
            assert(s5.tables.node_of(process, WITNESS_SUBCORE_SLOT) == nm);
            assert(s5.is_cap(nm));
            assert(s5.tables.has_slot(&s5.list, process, WITNESS_THREAD_SLOT));
            Self::lemma_caps_frame(s4, s5, nm, nm, nt);
            assert(s5.is_cap(nt) && s5.payload_of(nt) == thread_of(bt));
            assert(!s5.cap_dead(nt));
            assert(s5.can_control(process, WITNESS_THREAD_SLOT));
            assert(3usize < MAX_DEPTH) by (compute_only);
            assert(s5.holds_core(process, WITNESS_SUBCORE_SLOT, 3));
            assert(s5.can_place(process, WITNESS_THREAD_SLOT, WITNESS_SUBCORE_SLOT, 3));
            assert(s5.root_live(process));
            s5.lemma_placement_node_apart(bt);
            assert(!s5.list.nodes@[pn as int].live);
            assert(pn != nd && pn != nm && pn != b2);
        }

        // Place the thread on core 0 at priority 3 through the second, then start it.
        let placed = self.place(process, WITNESS_THREAD_SLOT, WITNESS_SUBCORE_SLOT, 3);
        let ghost s6 = *self;
        proof {
            assert(placed);
            lemma_core_of(core_object(0));
            assert(core_of(core_object(0)) == 0);
            assert(Self::placed(s5, s6, nm, bt, Placement { core: 0, priority: 3 }));
            assert(s6.list.wf()) by {
                reveal(CapKernel::wf);
            }
            lemma_children_after_add(s5.list, s6.list, pn, nm);
            assert forall|y: usize| #[trigger] s6.list.is_child(nd, y) implies y == nm by {
                if y != pn {
                    assert(s5.list.is_child(nd, y));
                }
            }
            assert forall|y: usize| #[trigger] s6.list.is_child(nm, y) implies y == pn by {
                if y != pn {
                    assert(s5.list.is_child(nm, y));
                }
            }
            assert forall|y: usize| !#[trigger] s6.list.is_child(pn, y) by {
                if y != pn {
                    s5.list.lemma_dead_childless(pn, y);
                }
            }
            assert(s6.list.is_child(nm, pn));
            assert(s6.tables == s5.tables);
            assert(s6.list.nodes@[b2 as int].live == s5.list.nodes@[b2 as int].live);
            assert(s6.tables.has_slot(&s6.list, process, WITNESS_THREAD_SLOT));
            assert(s6.tables.node_of(process, WITNESS_THREAD_SLOT) == nt);
            assert(s6.is_cap(nt) && s6.payload_of(nt) == thread_of(bt));
            assert(!s6.cap_dead(nt));
            assert(s6.can_control(process, WITNESS_THREAD_SLOT));
            assert(s6.can_start(process, WITNESS_THREAD_SLOT));
            assert(s6.flush_epoch == 0);
        }
        let started = self.start(process, WITNESS_THREAD_SLOT);
        let ghost s7 = *self;
        let at = Position { through: None, index: WITNESS_CORE_SLOT };
        proof {
            assert(started);
            assert(Self::state_written(s6, s7, bt, ThreadState::Runnable { core: 0 }));
            assert(s7.list == s6.list && s7.tables == s6.tables);
            assert(s7.threads.records@[bt].value().state == (ThreadState::Runnable { core: 0 }));
            assert(s7.threads.records@[bt].value().placement == Some(Placement { core: 0, priority: 3 }));
            assert(s7.tables.has_slot(&s7.list, process, WITNESS_CORE_SLOT));
            assert(s7.tables.node_of(process, WITNESS_CORE_SLOT) == nd);
            assert(s7.is_cap(nd));
            assert(s7.cap_at(process, at) == Some(nd));
            assert(s7.root_live(process));
            assert(s7.flush_epoch == 0);
        }

        // Revoke the first: it takes the second and the placement below it.
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let done = self.revoke(process, at, Tracked(&mut steps));
        proof {
            let s8 = *self;
            assert(!(done is Refused));
            assert(s8.list.wf()) by {
                reveal(CapKernel::wf);
            }
            let gone = choose|gone: Seq<usize>| revoked_seq(s7.list, s8.list, nd, gone);
            // Every node the revoke took was below nd, so it was the second capability or the
            // placement, and it took at most two.
            assert forall|i: int| 0 <= i < gone.len() implies #[trigger] gone[i] == nm || gone[i] == pn by {
                lemma_below_two(s7.list, nd, nm, pn, gone[i]);
            }
            if gone.len() > 2 {
                assert(gone[0] == nm || gone[0] == pn);
                assert(gone[1] == nm || gone[1] == pn);
                assert(gone[2] == nm || gone[2] == pn);
                assert(gone[0] != gone[1] && gone[0] != gone[2] && gone[1] != gone[2]);
            }
            assert(s7.list.seq@.len() - s8.list.seq@.len() <= 2);
            assert(s8.flush_epoch <= 2);
            assert(done is Done);
            assert(Self::cap_revoked_at(s7, s8, process, at));
            // The placement went: live, its parent nm would be live and listed, a child of nd.
            if s8.list.nodes@[pn as int].live {
                s8.lemma_placement_node_apart(bt);
                assert(has(s8.list.seq@, pn));
                lemma_has(s8.list.seq@, pn);
                let k = choose|k: int| 0 <= k < s8.list.seq@.len() && s8.list.seq@[k] == pn;
                assert(k != 0);
                assert(s8.list.parent@.contains_key(pn));
                assert(s8.list.parent@[pn] == nm);
                s8.list.lemma_parent_live(pn);
                assert(has(s8.list.seq@, nm));
                lemma_has(s8.list.seq@, nm);
                let j = choose|j: int| 0 <= j < s8.list.seq@.len() && s8.list.seq@[j] == nm;
                assert(j != 0);
                assert(s8.list.parent@[nm] == nd);
                assert(s8.list.is_child(nd, nm));
            }
            assert(!s8.list.nodes@[pn as int].live);
            assert(Self::threads_revoked(s7, s8));
            assert(s7.threads.records@.contains_key(bt));
            assert(bt + 1 < NODE_SPACE);
            assert(s8.threads.records@[bt].value().placement is None);
            assert(s8.threads.records@[bt].value().state is Inactive);
        }
        (placed, started, done)
    }
}

} // verus!
