//! The witness that a creator can build a process that holds a capability it chose and has a thread
//! bound to it: from the state boot leaves, the root gives itself a leaf, retypes a process and a
//! thread bound to it, retypes a leaf into the new process's table and derives an untyped into it, and
//! every step is proven to succeed. Only Verus compiles this module, so no image contains it. See
//! design/process-holds-capabilities/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_kernel::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::derive::*;
use crate::capability::destroy::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::position::*;
use crate::capability::process::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;

/// The index of the root's table the new process's capability goes in: slot 1 of root entry 2, the
/// leaf the witness gives the root first.
pub const WITNESS_PROCESS_SLOT: usize = 257;

/// The index of the root's table the new thread's capability goes in: slot 2 of root entry 2.
pub const WITNESS_THREAD_SLOT: usize = 258;

/// The index of the new process's table the derived capability goes in: slot 1 of its root entry 0.
pub const WITNESS_CHILD_SLOT: usize = 1;

/// The tables the runs need are never fewer than none.
proof fn lemma_tables_bound_nonneg(runs: Seq<ImageRun>)
    ensures
        0 <= image_tables_bound(runs),
    decreases runs.len(),
{
    if runs.len() > 0 {
        lemma_tables_bound_nonneg(runs.drop_last());
        let run = runs.last();
        let v = run.virt as int;
        lemma_div_is_ordered(v - 1, v + run.pages - 1, PAGES_PER_2M as int);
        lemma_fundamental_div_mod(v, 512);
        lemma_fundamental_div_mod(v - 1, 512);
        lemma_mod_bound(v, 512);
        lemma_mod_bound(v - 1, 512);
        assert(run_regions(run) >= 0);
    }
}

/// Page k of the order-3 block at b is its k-th page, in the 2M and 1G regions its first page is in,
/// and at an even k starts an order-1 block; the next order-3 block starts 8 pages on.
proof fn lemma_block_page(b: usize, k: int)
    requires
        b % 32768 == 0,
        0 <= k < 8,
    ensures
        (b + k * 4096) / 4096 == b / 4096 + k,
        (b + 32768) / 4096 == b / 4096 + 8,
        region_2m(b / 4096 + k) == region_2m((b / 4096) as int),
        region_1g(b / 4096 + k) == region_1g((b / 4096) as int),
        k % 2 == 0 ==> (b + k * 4096) % 8192 == 0,
{
    let q = b as int / 32768;
    lemma_fundamental_div_mod(b as int, 32768);
    assert(b == 32768 * q);
    lemma_fundamental_div_mod_converse(b + k * 4096, 4096, 8 * q + k, 0);
    lemma_fundamental_div_mod_converse(b as int, 4096, 8 * q, 0);
    lemma_fundamental_div_mod_converse(b + 32768, 4096, 8 * q + 8, 0);
    lemma_fundamental_div_mod(q, 64);
    lemma_mod_pos_bound(q, 64);
    lemma_fundamental_div_mod_converse(8 * q + k, 512, q / 64, 8 * (q % 64) + k);
    lemma_fundamental_div_mod_converse(8 * q, 512, q / 64, 8 * (q % 64));
    lemma_fundamental_div_mod(q, 32768);
    lemma_mod_pos_bound(q, 32768);
    lemma_fundamental_div_mod_converse(8 * q + k, 262144, q / 32768, 8 * (q % 32768) + k);
    lemma_fundamental_div_mod_converse(8 * q, 262144, q / 32768, 8 * (q % 32768));
    if k % 2 == 0 {
        lemma_fundamental_div_mod(k, 2);
        lemma_fundamental_div_mod_converse(b + k * 4096, 8192, 4 * q + k / 2, 0);
    }
}

impl CapKernel {
    /// From the state boot leaves, as the root at `process`, with the order-3 block at `base` the first
    /// of two free ones past those boot's tables took from the first untyped: retype a leaf into root
    /// entry 2 of the root's table at the second block's first two pages, a process at `base` into
    /// slot 1 of that leaf, a thread at the second block's next two pages into slot 2, bound to the
    /// process, a leaf at its next two into root entry 0 of the process's table, through the process
    /// capability, and derive an untyped over its last two pages from the root's first untyped into
    /// slot 1 of that leaf, through the process capability. Every step succeeds, and at the end the
    /// new process is not the root, holds the derived capability, the root's untyped's child, and has
    /// the thread bound to it.
    pub fn witness_process_holds_capability(
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
        base: usize,
    ) -> (ret: bool)
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@),
            image_tables_bound(image@) + 2 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
        ensures
            ret,
            ({
                let first = page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]);
                let u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
                let child = (base + 49153) as usize;
                let thread = (base + 40960) as usize;
                &&& final(self).wf()
                &&& base != process
                &&& final(self).view().holds(base, child)
                &&& final(self).list.is_child(u, child)
                &&& final(self).payload_of(child) == child_of(first, UNTYPED_RIGHTS, (base + 57344) as usize, 1)
                &&& bound_threads(&final(self).list, &final(self).tables).contains_key(thread)
                &&& bound_threads(&final(self).list, &final(self).tables)[thread] == base
            }),
    {
        hide(CapKernel::wf);
        let ghost s0 = *self;
        let ghost bs = runs_blocks(free@, MAX_ORDER as nat);
        let ghost first = page_block_payload(bs[0]);
        let ghost itb = image_tables_bound(image@);
        let ghost u = (leaf@ + ROOT_UNTYPED_SLOT) as usize;
        proof {
            lemma2_to64();
            lemma_tables_bound_nonneg(image@);
            // The root's first untyped, its process capability and its record.
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
            // The two free blocks, the second right after the first.
            assert(s0.root_untyped(process) == u);
            assert(s0.root_table_block(process, cursor_block(first.base, itb)));
            assert(s0.root_table_block(process, cursor_block(first.base, itb + 1)));
            lemma_pow2_pos(first.order as nat);
            lemma_fundamental_div_mod(block_bytes(first.order), 32768);
            lemma_mod_bound(block_bytes(first.order), 32768);
            assert((itb + 2) * 32768 <= block_bytes(first.order));
            assert(first.base + block_bytes(first.order) <= NODE_SPACE);
            assert(base == first.base + itb * 32768);
            assert(cursor_block(first.base, itb + 1) == base + 32768);
        }
        let b2 = base + 32768;
        let bt = b2 + 8192;
        let bl = b2 + 16384;
        let bd = b2 + 24576;
        proof {
            assert(block_bytes(3) == 32768);
            assert(block_bytes(1) == 8192);
            assert(base % 32768 == 0);
            assert(b2 % 32768 == 0);
            lemma_block_page(base, 0);
            lemma_block_page(b2, 0);
            lemma_block_page(b2, 2);
            lemma_block_page(b2, 4);
            lemma_block_page(b2, 6);
            assert(b2 / 4096 == base / 4096 + 8);
            assert(bt / 4096 == b2 / 4096 + 2);
            assert(bl / 4096 == b2 / 4096 + 4);
            assert(!s0.blocks.covered((base / 4096) as int));
            assert(!s0.blocks.covered((b2 / 4096) as int));
            assert(!s0.blocks.covered(b2 / 4096 + 2));
            assert(!s0.blocks.covered(b2 / 4096 + 4));
            assert forall|i: int| base / 4096 <= i < base / 4096 + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[base / 4096 + (i - base / 4096)].kind is Free);
            }
            assert forall|i: int| b2 / 4096 <= i < b2 / 4096 + 8 implies #[trigger] s0.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.pages@[b2 / 4096 + (i - b2 / 4096)].kind is Free);
            }
        }

        // A leaf for the root, in root entry 2 of its own table.
        let at1 = Position { through: None, index: 2 };
        proof {
            assert(s0.destination_at(process, None) == Some(process));
            assert(s0.tables.leaf(process, 2) == NO_LEAF);
            assert(s0.can_retype_under(process, ROOT_UNTYPED_SLOT, b2, 1));
            assert(s0.blocks.small_free((b2 / 4096) as int, 1));
            assert(s0.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2));
        }
        let ok1 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at1, b2);
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
            assert(index_ok(WITNESS_PROCESS_SLOT) && index_entry(WITNESS_PROCESS_SLOT) == 2);
            assert(index_ok(WITNESS_THREAD_SLOT) && index_entry(WITNESS_THREAD_SLOT) == 2);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_PROCESS_SLOT) as int].live);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(!s1.list.nodes@[s1.tables.node_of(process, WITNESS_THREAD_SLOT) as int].live);
            assert(s1.tables.node_of(process, WITNESS_PROCESS_SLOT) == b2 + 1);
            assert(s1.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(s1.processes == s0.processes);
            assert(s1.tables.roots@.contains_key(process));
            assert(s1.root_live(process));
            assert forall|i: int| base / 4096 <= i < base / 4096 + 8 || b2 / 4096 + 2 <= i < b2 / 4096 + 8
                implies #[trigger] s1.blocks.pages@[i].kind is Free by {
                assert(s0.blocks.tracks(i));
                assert(s0.blocks.pages@[i].kind is Free);
            }
        }

        // A process, in slot 1 of that leaf.
        proof {
            assert(s1.can_retype_under(process, ROOT_UNTYPED_SLOT, base, 3));
            assert(s1.blocks.small_free((base / 4096) as int, 3)) by {
                assert forall|k: int| 0 <= k < order_pages(3) implies #[trigger] s1.blocks.pages@[base / 4096 + k].kind is Free by {
                    assert(s1.blocks.pages@[(base / 4096 + k) as int].kind is Free);
                }
            }
            assert(s1.can_retype_block(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base, PROCESS_ORDER));
        }
        let ok2 = self.retype_process(process, ROOT_UNTYPED_SLOT, WITNESS_PROCESS_SLOT, base);
        let ghost s2 = *self;
        let ghost np = (b2 + 1) as usize;
        proof {
            assert(ok2);
            assert(Self::retype_keeps(s1, s2, np, (base / 4096) as int, 3, None));
            assert(s2.tables.roots@.contains_key(base));
            assert(s2.processes.records@.contains_key(base));
            assert(!s2.processes.records@[base].value().dead);
            assert(s2.payload_of(np) == process_of(base));
            assert(s2.payload_of(np).rights & right_bit(Right::Control) != 0);
            assert(s2.list.nodes@[np as int].depth == 2);
            assert(s2.view().holds(process, np));
            assert(s2.is_cap(np));
            // The root's table keeps its new leaf, which the new process's table lacks, so the two differ.
            assert(s1.tables.roots@.contains_key(process));
            assert(s2.tables.leaf(process, 2) == b2);
            assert(s2.tables.leaf(base, 2) == NO_LEAF);
            assert(base != process);
            // The untyped, the thread's slot and the root's record stay.
            assert(s1.tables.has_slot(&s1.list, process, ROOT_UNTYPED_SLOT));
            assert(s1.is_cap(u));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s2.is_cap(u) && s2.payload_of(u) == first && s2.list.nodes@[u as int].depth == 1);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s2.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s1.tables.has_slot(&s1.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_THREAD_SLOT));
            assert(s2.tables.node_of(process, WITNESS_THREAD_SLOT) == b2 + 2);
            assert(!s2.list.nodes@[(b2 + 2) as int].live);
            assert(s1.processes.records@.contains_key(process));
            assert(s2.processes.records@.contains_key(process));
            assert(s2.root_live(process));
            assert(s2.tables.roots@.contains_key(process));
            assert forall|i: int| b2 / 4096 + 2 <= i < b2 / 4096 + 8 implies #[trigger] s2.blocks.pages@[i].kind is Free by {
                assert(s1.blocks.tracks(i));
                assert(s1.blocks.pages@[i].kind is Free);
            }
        }

        // A thread, in slot 2 of the root's leaf, bound to the process.
        proof {
            assert(block_refs(&s2.blocks, BlockRef::Small(base / 4096)) == 1);
            assert(!s2.cap_dead(np));
            assert(s2.can_hold_thread(process, WITNESS_PROCESS_SLOT));
            assert(s2.can_retype_under(process, ROOT_UNTYPED_SLOT, bt, THREAD_ORDER));
            assert(s2.blocks.small_free((bt / 4096) as int, THREAD_ORDER as usize)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s2.blocks.pages@[bt / 4096 + k].kind is Free by {
                    assert(s2.blocks.pages@[(b2 / 4096 + 2 + k) as int].kind is Free);
                }
            }
            assert(s2.can_retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT));
        }
        let ok3 = self.retype_thread(process, ROOT_UNTYPED_SLOT, WITNESS_THREAD_SLOT, bt, WITNESS_PROCESS_SLOT);
        let ghost s3 = *self;
        proof {
            assert(ok3);
            assert(s2.payload_of(s2.tables.node_of(process, WITNESS_PROCESS_SLOT)).base == base);
            assert(bound_threads(&s3.list, &s3.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(Self::retype_keeps(s2, s3, (b2 + 2) as usize, (bt / 4096) as int, 1, None));
            assert(s2.tables.has_slot(&s2.list, process, ROOT_UNTYPED_SLOT));
            assert(s2.is_cap(u));
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s3.is_cap(u) && s3.payload_of(u) == first && s3.list.nodes@[u as int].depth == 1);
            assert(s2.tables.has_slot(&s2.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s3.is_cap(np) && s3.payload_of(np) == process_of(base));
            assert(s2.processes.records@.contains_key(process));
            assert(s3.processes.records@.contains_key(process));
            assert(s3.root_live(process));
            assert(s3.tables.roots@.contains_key(process));
            assert(s3.processes.records@.contains_key(base));
            assert(!s3.processes.records@[base].value().dead);
            assert(s3.tables.leaf(base, 0) == NO_LEAF);
            assert forall|i: int| b2 / 4096 + 4 <= i < b2 / 4096 + 6 implies #[trigger] s3.blocks.pages@[i].kind is Free by {
                assert(s2.blocks.tracks(i));
                assert(s2.blocks.pages@[i].kind is Free);
            }
        }

        // A leaf in root entry 0 of the new process's table, through the process capability.
        let at2 = Position { through: Some(WITNESS_PROCESS_SLOT), index: 0 };
        proof {
            assert(s3.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.destination_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(s3.can_retype_under(process, ROOT_UNTYPED_SLOT, bl, 1));
            assert(s3.blocks.small_free((bl / 4096) as int, 1)) by {
                assert forall|k: int| 0 <= k < order_pages(1) implies #[trigger] s3.blocks.pages@[bl / 4096 + k].kind is Free by {
                    assert(s3.blocks.pages@[(b2 / 4096 + 4 + k) as int].kind is Free);
                }
            }
            assert(s3.can_retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl));
        }
        let ok4 = self.retype_leaf(process, ROOT_UNTYPED_SLOT, at2, bl);
        let ghost s4 = *self;
        let ghost child = (bl + 1) as usize;
        proof {
            assert(ok4);
            assert(Self::leaf_retyped(s3, s4, process, ROOT_UNTYPED_SLOT, at2, bl));
            assert(s4.tables.leaf(base, 0) == bl);
            assert(index_ok(WITNESS_CHILD_SLOT) && index_entry(WITNESS_CHILD_SLOT) == 0);
            assert(s4.tables.has_slot(&s4.list, base, WITNESS_CHILD_SLOT));
            assert(s4.tables.node_of(base, WITNESS_CHILD_SLOT) == child);
            assert(!s4.list.nodes@[child as int].live);
            assert(s4.processes == s3.processes);
            assert(s3.tables.has_slot(&s3.list, process, ROOT_UNTYPED_SLOT));
            assert(s3.is_cap(u));
            assert(s4.tables.has_slot(&s4.list, process, ROOT_UNTYPED_SLOT));
            assert(s4.tables.node_of(process, ROOT_UNTYPED_SLOT) == u);
            assert(s4.is_cap(u) && s4.payload_of(u) == first && s4.list.nodes@[u as int].depth == 1);
            assert(s3.tables.has_slot(&s3.list, process, WITNESS_PROCESS_SLOT));
            assert(s3.is_cap(np));
            assert(s4.tables.has_slot(&s4.list, process, WITNESS_PROCESS_SLOT));
            assert(s4.tables.node_of(process, WITNESS_PROCESS_SLOT) == np);
            assert(s4.is_cap(np) && s4.payload_of(np) == process_of(base));
            assert(s4.root_live(process));
            assert(s4.tables.roots@.contains_key(process));
        }

        // An untyped over the second block's last two pages, derived from the root's untyped into slot 1
        // of the new process's leaf, through the process capability.
        let at3 = Position { through: Some(WITNESS_PROCESS_SLOT), index: WITNESS_CHILD_SLOT };
        proof {
            assert(s4.table_at(process, Some(WITNESS_PROCESS_SLOT)) == Some(base));
            assert(!s4.cap_dead(u));
            assert(names_block(first.kind));
            assert(UNTYPED_RIGHTS & !UNTYPED_RIGHTS == 0) by (compute_only);
            assert(UNTYPED_RIGHTS & right_bit(Right::Control) == 0) by (compute_only);
            assert(block_within(bd, 1, first));
            assert(narrows(child_of(first, UNTYPED_RIGHTS, bd, 1), first));
            assert(s4.can_derive_between(process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s4.can_derive_at(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1));
        }
        let ok5 = self.derive(process, ROOT_UNTYPED_SLOT, at3, UNTYPED_RIGHTS, bd, 1);
        proof {
            let s5 = *self;
            assert(ok5);
            assert(Self::cap_derived_between(s4, s5, process, ROOT_UNTYPED_SLOT, base, WITNESS_CHILD_SLOT, UNTYPED_RIGHTS, bd, 1));
            assert(s5.view().holds(base, child));
            assert(s5.list.is_child(u, child));
            assert(s5.payload_of(child) == child_of(first, UNTYPED_RIGHTS, bd, 1));
            assert(bound_threads(&s5.list, &s5.tables) == bound_threads(&s2.list, &s2.tables).insert(bt, base));
            assert(child == base + 49153);
            assert(bt == base + 40960);
            assert(bd == base + 57344);
        }
        ok1 && ok2 && ok3 && ok4 && ok5
    }
}

} // verus!
