// SPDX-License-Identifier: MIT

//! The capability kernel's state, which each later module extends. `wf` holds at every step boundary:
//! a long operation returns to the caller between steps, so other cores interleave only where it
//! holds. One lock covers all of this. Per-CPU state outside the lock (stacks, the GDT and TSS) lives
//! in kernel/src's Cpu. See design/one-lock-bounded-steps/ and
//! design/flush-without-waiting/.
use vstd::prelude::*;

verus! {

use crate::arch::{flush_every_context, invalidate_iommu_all};
use crate::arch::{BaseRegister, IotlbModel, TlbModel};
#[cfg(verus_keep_ghost)]
use crate::arch::tag_written;
use crate::array::Array;
use crate::capability::block::*;
#[cfg(verus_keep_ghost)]
use crate::capability::derive::badges_inherited;
use crate::capability::device::*;
use crate::capability::endpoint::*;
use crate::capability::reply::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
use crate::capability::mapping::*;
use crate::capability::list::*;
use crate::capability::steps::Steps;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::Tables;
use crate::capability::process::*;
#[cfg(verus_keep_ghost)]
use crate::capability::schedule::*;
use crate::capability::thread::*;
use crate::capability::zero::*;
use crate::define::*;
use crate::pptr::PointsTo;

/// One core's view under the lock.
#[derive(Clone, Copy)]
pub struct CoreState {
    /// Only this core writes it. A stop from elsewhere is a request this core acts on.
    pub current_thread: Option<usize>,
    /// The flush epoch this core has acknowledged.
    pub acked_epoch: usize,
    /// A space's id on this core is valid only at this generation. It is never zero.
    pub generation: usize,
    /// The next PCID to hand out at this generation. The PCIDs the core may hold entries under are
    /// below it: tags_wf.
    pub next_pcid: usize,
    /// The space whose root this core's page-table base register names, or None for the kernel's own
    /// root. Only switch_space writes it, in the step that writes the
    /// register through the core's BaseRegister: registers_wf. See design/teardown-driven-by-retype/.
    pub space: Option<usize>,
}

/// The largest generation a space's word can hold above its 12 bits of PCID.
pub const ID_GENERATION_MAX: usize = 0xF_FFFF_FFFF_FFFF;

/// The PCID or ASID a base register naming no space is written under. A space is handed 1 and up, so
/// no space holds it: CapKernel::lemma_kernel_tag.
pub const KERNEL_TAG: usize = 0;

/// acknowledge's bound in the step counter: none, since it flushes its own core and writes that core's
/// state, and runs no loop.
/// See design/one-lock-bounded-steps/.
pub const ACKNOWLEDGE_STEPS: usize = 0;

/// flush_iommu's bound in the step counter: one, the wait for the IOMMU's invalidate, which the IOMMU
/// sets and the kernel's state does not.
/// See design/one-lock-bounded-steps/.
pub const FLUSH_IOMMU_STEPS: usize = 1;

pub open spec fn id_generation(word: usize) -> usize {
    (word / PCID_MAX) as usize
}

pub open spec fn id_pcid(word: usize) -> usize {
    (word % PCID_MAX) as usize
}

/// A core in this state has loaded a space since boot: loading one hands out a tag, which moves the
/// core's next tag or, once they run out, its generation from boot's. A core that has not is on no
/// space's list (ids_wf), so it holds no translation of any space: CapKernel::lemma_loaded_a_space.
pub open spec fn has_loaded(state: CoreState) -> bool {
    state.generation != 1 || state.next_pcid != 1
}

impl CoreState {
    /// Whether this core has loaded a space since boot. A free asks only such a core for its
    /// acknowledgement, and only such a core is sent the flush IPI: design/flush-without-waiting/.
    pub fn loaded_a_space(&self) -> (ret: bool)
        ensures
            ret == has_loaded(*self),
    {
        self.generation != 1 || self.next_pcid != 1
    }
}

/// Space s holds a valid id on core c.
pub open spec fn holds_id(cores: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int, s: usize) -> bool {
    &&& lists.contains_key(s)
    &&& id_generation(lists[s].value().ids@[c]) == cores[c].generation
}

/// A base register that names space s names one this core is listed on, that is not retired, and that
/// holds a valid id at the core's generation `generation`, so the tag the register was written under is
/// still s's and no other space's.
pub open spec fn names_wf(space: Option<usize>, generation: usize, lists: Map<usize, PointsTo<SpaceCores>>, c: int) -> bool {
    match space {
        None => true,
        Some(s) => {
            &&& lists.contains_key(s)
            &&& core_listed(lists[s].value().list, c)
            &&& lists[s].value().retired == 0
            &&& id_generation(lists[s].value().ids@[c]) == generation
        },
    }
}

/// No word is ahead of its core's generation, so a new generation leaves no id valid. A valid id is one
/// already handed out, and no two spaces hold one. A core's base register names a space it is listed
/// on, that is not retired and that holds a valid id there. A core on a space's list has loaded a
/// space, which its own state shows.
#[verifier::opaque]
pub open spec fn ids_wf(cores: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>) -> bool {
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> {
        &&& 1 <= (#[trigger] cores[c]).generation <= ID_GENERATION_MAX
        &&& 1 <= cores[c].next_pcid <= PCID_MAX
    }
    &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS && lists.contains_key(s) ==> #[trigger] id_generation(lists[s].value().ids@[c]) <= cores[c].generation
    &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, lists, c, s) ==> {
        &&& 1 <= id_pcid(lists[s].value().ids@[c])
        &&& id_pcid(lists[s].value().ids@[c]) < cores[c].next_pcid
    }
    &&& forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, lists, c, s) && #[trigger] holds_id(cores, lists, c, r)
        ==> id_pcid(lists[s].value().ids@[c]) != id_pcid(lists[r].value().ids@[c])
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] names_wf(cores[c].space, cores[c].generation, lists, c)
    &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS && lists.contains_key(s) && #[trigger] core_listed(lists[s].value().list, c)
        ==> has_loaded(cores[c])
}

/// Core c's base register names `space`: for Some(s), s's root under the tag the core writes for the id
/// s holds on c (tag_written: that id where the core tags its TLB, KERNEL_TAG where it does not); for
/// None, under KERNEL_TAG, the kernel's own root, the one every core boots on.
pub open spec fn register_names(r: BaseRegister, space: Option<usize>, lists: Map<usize, PointsTo<SpaceCores>>, c: int, kernel_root: usize) -> bool {
    &&& r.core() == c
    &&& match space {
        Some(s) => {
            &&& lists.contains_key(s)
            &&& r.root() == s + SPACE_ROOT_PAGE * PAGE_SZ
            &&& r.tag() == tag_written(c, id_pcid(lists[s].value().ids@[c]))
        },
        None => {
            &&& r.tag() == KERNEL_TAG
            &&& r.root() == kernel_root
        },
    }
}

/// The cores' TLB model as boot makes it: one set of entries and one of tags per core, each empty,
/// since no space is loaded yet.
pub open spec fn boot_tlb(tlb: TlbModel) -> bool {
    &&& tlb.len() == NUM_CPUS
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] tlb[c] == Set::<TlbEntry>::empty()
    &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] tlb.tags(c) == Set::<usize>::empty()
}

/// A core may hold entries only under a PCID it has handed out at its generation, so the one it hands
/// out next is under none, and a new generation, which hands them out again from the start, needs the
/// core's tags emptied, which only its flush does.
pub open spec fn tags_wf(cores: Seq<CoreState>, tlb: TlbModel) -> bool {
    forall|c: int, p: usize| 0 <= c < NUM_CPUS && #[trigger] tlb.tags(c).contains(p) ==> p < cores[c].next_pcid
}

/// The IOMMUs' IOTLB model as boot makes it: one set per IOMMU, each empty, since nothing is unmapped yet.
pub open spec fn boot_iotlb(iotlb: IotlbModel) -> bool {
    &&& iotlb.len() == NUM_IOMMUS
    &&& forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] iotlb[i] == Set::<TlbEntry>::empty()
}

/// Every core's base register as boot leaves it: naming `kernel_root` under KERNEL_TAG.
pub open spec fn boot_registers(registers: Map<int, BaseRegister>, kernel_root: usize) -> bool {
    forall|c: int| 0 <= c < NUM_CPUS ==> {
        &&& #[trigger] registers.contains_key(c)
        &&& registers[c].core() == c
        &&& registers[c].root() == kernel_root
        &&& registers[c].tag() == KERNEL_TAG
    }
}

/// The page of the root every core boots on stays Reserved when the blocks track it: boot hands it
/// to no block, as kernel_init requires, and nothing after boot types a Reserved page. So it lies in
/// no block, and no space's root is it (lemma_none_names_no_root).
pub open spec fn kernel_root_reserved(blocks: &BlockTable, kernel_root: usize) -> bool {
    blocks.tracks_addr(kernel_root) ==> blocks.pages@[(kernel_root / PAGE_SZ) as int].kind is Reserved
}

/// The kernel root's page, when the blocks track it, is none of the `n` pages from `start`: a boot step
/// handing those pages to the blocks leaves the root's page Reserved.
pub open spec fn kernel_root_apart(blocks: &BlockTable, kernel_root: usize, start: int, n: int) -> bool {
    blocks.tracks_addr(kernel_root) ==> !(start <= kernel_root / PAGE_SZ < start + n)
}

/// The kernel holds each core's base register, and what each last wrote is what the core's record
/// says it names. Only switch_space writes a register, and it writes the record in the same step, so
/// no write the record does not show can happen: design/teardown-driven-by-retype/.
#[verifier::opaque]
pub open spec fn registers_wf(registers: Map<int, BaseRegister>, cores: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, kernel_root: usize) -> bool {
    forall|c: int| 0 <= c < NUM_CPUS ==> {
        &&& #[trigger] registers.contains_key(c)
        &&& register_names(registers[c], cores[c].space, lists, c, kernel_root)
    }
}

/// The registers still name what the records say after a step that names the same space on every core
/// and keeps the tag each named space holds there.
pub proof fn lemma_registers_kept(
    registers: Map<int, BaseRegister>,
    pre: Seq<CoreState>,
    post: Seq<CoreState>,
    pre_lists: Map<usize, PointsTo<SpaceCores>>,
    post_lists: Map<usize, PointsTo<SpaceCores>>,
    kernel_root: usize,
)
    requires
        registers_wf(registers, pre, pre_lists, kernel_root),
        forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] post[c]).space == pre[c].space,
        forall|c: int| 0 <= c < NUM_CPUS && (#[trigger] post[c]).space is Some && pre_lists.contains_key(post[c].space->0) ==> {
            &&& post_lists.contains_key(post[c].space->0)
            &&& id_pcid(post_lists[post[c].space->0].value().ids@[c]) == id_pcid(pre_lists[post[c].space->0].value().ids@[c])
        },
    ensures
        registers_wf(registers, post, post_lists, kernel_root),
{
    reveal(registers_wf);
    assert forall|c: int| 0 <= c < NUM_CPUS implies {
        &&& #[trigger] registers.contains_key(c)
        &&& register_names(registers[c], post[c].space, post_lists, c, kernel_root)
    } by {
        assert(registers.contains_key(c));
        assert(register_names(registers[c], pre[c].space, pre_lists, c, kernel_root));
        assert(post[c].space == pre[c].space);
    }
}

/// The registers still name what the records say after a change to the lists that keeps each space a
/// register names.
pub proof fn lemma_registers_lists(
    registers: Map<int, BaseRegister>,
    cores: Seq<CoreState>,
    pre: Map<usize, PointsTo<SpaceCores>>,
    post: Map<usize, PointsTo<SpaceCores>>,
    kernel_root: usize,
)
    requires
        registers_wf(registers, cores, pre, kernel_root),
        forall|c: int| 0 <= c < NUM_CPUS && (#[trigger] cores[c]).space is Some && pre.contains_key(cores[c].space->0) ==> {
            &&& post.contains_key(cores[c].space->0)
            &&& post[cores[c].space->0] == pre[cores[c].space->0]
        },
    ensures
        registers_wf(registers, cores, post, kernel_root),
{
    lemma_registers_kept(registers, cores, cores, pre, post, kernel_root);
}

/// A word holds its generation and PCID.
pub proof fn lemma_id_word(g: usize, p: usize)
    requires
        g <= ID_GENERATION_MAX,
        p < PCID_MAX,
    ensures
        g * PCID_MAX + p <= usize::MAX,
        id_generation((g * PCID_MAX + p) as usize) == g,
        id_pcid((g * PCID_MAX + p) as usize) == p,
{
    assert(g * PCID_MAX + p <= usize::MAX) by (nonlinear_arith)
        requires g <= ID_GENERATION_MAX, p < PCID_MAX;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g * PCID_MAX + p, PCID_MAX as int, g as int, p as int);
}

/// The ids are well formed after a change to the lists that keeps every space's words and leaves each
/// base register naming a space it may name.
pub proof fn lemma_ids_same(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>)
    requires
        ids_wf(cores, pre),
        post.dom() == pre.dom(),
        forall|r: usize| #[trigger] post.contains_key(r) ==> post[r].value().ids@ == pre[r].value().ids@,
        forall|r: usize| #[trigger] post.contains_key(r) ==> post[r].value().list == pre[r].value().list,
        forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] names_wf(cores[c].space, cores[c].generation, post, c),
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && post.contains_key(r) && #[trigger] core_listed(post[r].value().list, d)
        implies has_loaded(cores[d]) by {
        assert(pre.contains_key(r));
        assert(core_listed(pre[r].value().list, d));
    }
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && post.contains_key(r) implies #[trigger] id_generation(post[r].value().ids@[d]) <= cores[d].generation by {
        assert(pre.contains_key(r));
    }
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(cores, post, d, r) implies {
        &&& 1 <= id_pcid(post[r].value().ids@[d])
        &&& id_pcid(post[r].value().ids@[d]) < cores[d].next_pcid
    } by {
        assert(holds_id(cores, pre, d, r));
    }
    assert forall|d: int, r: usize, q: usize| 0 <= d < NUM_CPUS && r != q && #[trigger] holds_id(cores, post, d, r) && #[trigger] holds_id(cores, post, d, q)
        implies id_pcid(post[r].value().ids@[d]) != id_pcid(post[q].value().ids@[d]) by {
        assert(holds_id(cores, pre, d, r));
        assert(holds_id(cores, pre, d, q));
    }
}

/// The ids after space s's word on core c becomes w: its generation current, its PCID handed out and
/// held by no other space.
pub proof fn lemma_id_loaded(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, c: int, s: usize, w: usize)
    requires
        ids_wf(cores, pre),
        0 <= c < NUM_CPUS,
        pre.contains_key(s),
        post == pre.insert(s, post[s]),
        post[s].value().ids@ == pre[s].value().ids@.update(c, w),
        id_generation(w) == cores[c].generation,
        1 <= id_pcid(w) < cores[c].next_pcid,
        forall|r: usize| r != s && #[trigger] holds_id(cores, pre, c, r) ==> id_pcid(pre[r].value().ids@[c]) != id_pcid(w),
        forall|d: int| 0 <= d < NUM_CPUS && core_listed(pre[s].value().list, d) ==> #[trigger] core_listed(post[s].value().list, d),
        forall|d: int| 0 <= d < NUM_CPUS && #[trigger] core_listed(post[s].value().list, d) ==> d == c || core_listed(pre[s].value().list, d),
        post[s].value().retired == 0,
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && post.contains_key(r) && #[trigger] core_listed(post[r].value().list, d)
        implies has_loaded(cores[d]) by {
        if r != s {
            assert(pre.contains_key(r));
            assert(post[r] == pre[r]);
            assert(core_listed(pre[r].value().list, d));
        } else if d != c {
            assert(core_listed(pre[s].value().list, d));
        } else {
            assert(cores[c].next_pcid >= 2);
        }
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] names_wf(cores[d].space, cores[d].generation, post, d) by {
        assert(names_wf(cores[d].space, cores[d].generation, pre, d));
        if cores[d].space == Some(s) {
            assert(core_listed(post[s].value().list, d));
        }
    }
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && post.contains_key(r) implies #[trigger] id_generation(post[r].value().ids@[d]) <= cores[d].generation by {
        assert(pre.contains_key(r));
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
        }
    }
    assert forall|d: int, r: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(cores, post, d, r) implies {
        &&& 1 <= id_pcid(post[r].value().ids@[d])
        &&& id_pcid(post[r].value().ids@[d]) < cores[d].next_pcid
    } by {
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
            assert(holds_id(cores, pre, d, r));
        }
    }
    assert forall|d: int, r: usize, q: usize| 0 <= d < NUM_CPUS && r != q && #[trigger] holds_id(cores, post, d, r) && #[trigger] holds_id(cores, post, d, q)
        implies id_pcid(post[r].value().ids@[d]) != id_pcid(post[q].value().ids@[d]) by {
        if !(d == c && r == s) {
            assert(post[r].value().ids@[d] == pre[r].value().ids@[d]);
        }
        if !(d == c && q == s) {
            assert(post[q].value().ids@[d] == pre[q].value().ids@[d]);
        }
        if d == c && r == s {
            assert(holds_id(cores, pre, c, q));
        } else if d == c && q == s {
            assert(holds_id(cores, pre, c, r));
        } else {
            assert(holds_id(cores, pre, d, r));
            assert(holds_id(cores, pre, d, q));
        }
    }
}

/// The ids after core c's state changes with its generation kept: more PCIDs handed out leaves every id
/// valid.
pub proof fn lemma_ids_core_step(pre: Seq<CoreState>, post: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int)
    requires
        ids_wf(pre, lists),
        0 <= c < NUM_CPUS,
        post.len() == pre.len(),
        forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post[d] == pre[d],
        post[c].generation == pre[c].generation,
        pre[c].next_pcid <= post[c].next_pcid <= PCID_MAX,
        post[c].space == pre[c].space,
    ensures
        ids_wf(post, lists),
        forall|s: usize| #[trigger] holds_id(post, lists, c, s) == holds_id(pre, lists, c, s),
{
    reveal(ids_wf);
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) && #[trigger] core_listed(lists[s].value().list, d)
        implies has_loaded(post[d]) by {
        assert(has_loaded(pre[d]));
        assert(1 <= pre[d].next_pcid <= PCID_MAX);
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] names_wf(post[d].space, post[d].generation, lists, d) by {
        assert(names_wf(pre[d].space, pre[d].generation, lists, d));
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS implies #[trigger] holds_id(post, lists, d, s) == holds_id(pre, lists, d, s) by {
        assert(post[d].generation == pre[d].generation);
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies {
        &&& 1 <= (#[trigger] post[d]).generation <= ID_GENERATION_MAX
        &&& 1 <= post[d].next_pcid <= PCID_MAX
    } by {
        assert(1 <= pre[d].generation <= ID_GENERATION_MAX);
        assert(1 <= pre[d].next_pcid <= PCID_MAX);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) implies #[trigger] id_generation(lists[s].value().ids@[d]) <= post[d].generation by {
        assert(id_generation(lists[s].value().ids@[d]) <= pre[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(post, lists, d, s) implies {
        &&& 1 <= id_pcid(lists[s].value().ids@[d])
        &&& id_pcid(lists[s].value().ids@[d]) < post[d].next_pcid
    } by {
        assert(holds_id(pre, lists, d, s));
    }
    assert forall|d: int, s: usize, r: usize| 0 <= d < NUM_CPUS && s != r && #[trigger] holds_id(post, lists, d, s) && #[trigger] holds_id(post, lists, d, r)
        implies id_pcid(lists[s].value().ids@[d]) != id_pcid(lists[r].value().ids@[d]) by {
        assert(holds_id(pre, lists, d, s));
        assert(holds_id(pre, lists, d, r));
    }
}

/// The ids after core c starts a new generation with nothing used: no space's id is valid there, so its
/// base register must name no space.
pub proof fn lemma_ids_new_generation(pre: Seq<CoreState>, post: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int)
    requires
        ids_wf(pre, lists),
        0 <= c < NUM_CPUS,
        post.len() == pre.len(),
        forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post[d] == pre[d],
        post[c].generation == pre[c].generation + 1,
        post[c].generation <= ID_GENERATION_MAX,
        1 <= post[c].next_pcid <= PCID_MAX,
        pre[c].space is None,
        post[c].space == pre[c].space,
    ensures
        ids_wf(post, lists),
        forall|s: usize| !#[trigger] holds_id(post, lists, c, s),
{
    reveal(ids_wf);
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) && #[trigger] core_listed(lists[s].value().list, d)
        implies has_loaded(post[d]) by {
        assert(has_loaded(pre[d]));
        assert(1 <= pre[d].generation <= ID_GENERATION_MAX);
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] names_wf(post[d].space, post[d].generation, lists, d) by {
        assert(names_wf(pre[d].space, pre[d].generation, lists, d));
    }
    assert forall|s: usize| !#[trigger] holds_id(post, lists, c, s) by {
        if lists.contains_key(s) {
            assert(id_generation(lists[s].value().ids@[c]) <= pre[c].generation);
        }
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies {
        &&& 1 <= (#[trigger] post[d]).generation <= ID_GENERATION_MAX
        &&& 1 <= post[d].next_pcid <= PCID_MAX
    } by {
        assert(1 <= pre[d].generation <= ID_GENERATION_MAX);
        assert(1 <= pre[d].next_pcid <= PCID_MAX);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) implies #[trigger] id_generation(lists[s].value().ids@[d]) <= post[d].generation by {
        assert(id_generation(lists[s].value().ids@[d]) <= pre[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(post, lists, d, s) implies {
        &&& 1 <= id_pcid(lists[s].value().ids@[d])
        &&& id_pcid(lists[s].value().ids@[d]) < post[d].next_pcid
    } by {
        assert(d != c);
        assert(holds_id(pre, lists, d, s));
    }
    assert forall|d: int, s: usize, r: usize| 0 <= d < NUM_CPUS && s != r && #[trigger] holds_id(post, lists, d, s) && #[trigger] holds_id(post, lists, d, r)
        implies id_pcid(lists[s].value().ids@[d]) != id_pcid(lists[r].value().ids@[d]) by {
        assert(d != c);
        assert(holds_id(pre, lists, d, s));
        assert(holds_id(pre, lists, d, r));
    }
}

/// A new space's zero words hold no id, whatever the others hold.
pub proof fn lemma_ids_space_added(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, base: usize)
    requires
        ids_wf(cores, pre),
        !pre.contains_key(base),
        post == pre.insert(base, post[base]),
        forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] post[base].value().ids@[c] == 0usize,
        post[base].value().list == 0u32,
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) && #[trigger] core_listed(post[s].value().list, c)
        implies has_loaded(cores[c]) by {
        if s == base {
            crate::capability::space::lemma_no_core_listed(c as u32);
        } else {
            assert(pre.contains_key(s));
            assert(post[s] == pre[s]);
            assert(core_listed(pre[s].value().list, c));
        }
    }
    assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] names_wf(cores[c].space, cores[c].generation, post, c) by {
        assert(names_wf(cores[c].space, cores[c].generation, pre, c));
        if let Some(r) = cores[c].space {
            assert(post[r] == pre[r]);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies s != base && holds_id(cores, pre, c, s) by {
        if s == base {
            assert(post[base].value().ids@[c] == 0usize);
            assert(cores[c].generation >= 1);
            assert(id_generation(0usize) == 0);
        } else {
            assert(post[s] == pre[s]);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) implies #[trigger] id_generation(post[s].value().ids@[c]) <= cores[c].generation by {
        if s == base {
            assert(post[base].value().ids@[c] == 0usize);
            assert(id_generation(0usize) == 0);
            assert(cores[c].generation >= 1);
            assert(id_generation(post[s].value().ids@[c]) == 0);
        } else {
            assert(pre.contains_key(s));
            assert(post[s] == pre[s]);
            assert(id_generation(pre[s].value().ids@[c]) <= cores[c].generation);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies {
        &&& 1 <= id_pcid(post[s].value().ids@[c])
        &&& id_pcid(post[s].value().ids@[c]) < cores[c].next_pcid
    } by {
        assert(holds_id(cores, pre, c, s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, post, c, s) && #[trigger] holds_id(cores, post, c, r)
        implies id_pcid(post[s].value().ids@[c]) != id_pcid(post[r].value().ids@[c]) by {
        assert(holds_id(cores, pre, c, s));
        assert(holds_id(cores, pre, c, r));
        assert(post[s] == pre[s]);
        assert(post[r] == pre[r]);
    }
}

/// The ids after a space no base register names goes.
pub proof fn lemma_ids_space_removed(cores: Seq<CoreState>, pre: Map<usize, PointsTo<SpaceCores>>, post: Map<usize, PointsTo<SpaceCores>>, base: usize)
    requires
        ids_wf(cores, pre),
        post == pre.remove(base),
        forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] cores[c].space != Some(base),
    ensures
        ids_wf(cores, post),
{
    reveal(ids_wf);
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) && #[trigger] core_listed(post[s].value().list, c)
        implies has_loaded(cores[c]) by {
        assert(pre.contains_key(s));
        assert(post[s] == pre[s]);
        assert(core_listed(pre[s].value().list, c));
    }
    assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] names_wf(cores[c].space, cores[c].generation, post, c) by {
        assert(names_wf(cores[c].space, cores[c].generation, pre, c));
        assert(cores[c].space != Some(base));
        if let Some(r) = cores[c].space {
            assert(post[r] == pre[r]);
        }
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies s != base && holds_id(cores, pre, c, s) by {
        assert(post.contains_key(s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && post.contains_key(s) implies #[trigger] id_generation(post[s].value().ids@[c]) <= cores[c].generation by {
        assert(pre.contains_key(s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize| 0 <= c < NUM_CPUS && #[trigger] holds_id(cores, post, c, s) implies {
        &&& 1 <= id_pcid(post[s].value().ids@[c])
        &&& id_pcid(post[s].value().ids@[c]) < cores[c].next_pcid
    } by {
        assert(holds_id(cores, pre, c, s));
        assert(post[s] == pre[s]);
    }
    assert forall|c: int, s: usize, r: usize| 0 <= c < NUM_CPUS && s != r && #[trigger] holds_id(cores, post, c, s) && #[trigger] holds_id(cores, post, c, r)
        implies id_pcid(post[s].value().ids@[c]) != id_pcid(post[r].value().ids@[c]) by {
        assert(holds_id(cores, pre, c, s));
        assert(holds_id(cores, pre, c, r));
        assert(post[s] == pre[s]);
        assert(post[r] == pre[r]);
    }
}

/// The ids after core c's base register comes to name a space it may name.
pub proof fn lemma_ids_named(pre: Seq<CoreState>, post: Seq<CoreState>, lists: Map<usize, PointsTo<SpaceCores>>, c: int)
    requires
        ids_wf(pre, lists),
        0 <= c < NUM_CPUS,
        forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post[d] == pre[d],
        post[c].generation == pre[c].generation,
        post[c].next_pcid == pre[c].next_pcid,
        names_wf(post[c].space, post[c].generation, lists, c),
    ensures
        ids_wf(post, lists),
        forall|d: int, s: usize| 0 <= d < NUM_CPUS ==> #[trigger] holds_id(post, lists, d, s) == holds_id(pre, lists, d, s),
{
    reveal(ids_wf);
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) && #[trigger] core_listed(lists[s].value().list, d)
        implies has_loaded(post[d]) by {
        assert(has_loaded(pre[d]));
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] names_wf(post[d].space, post[d].generation, lists, d) by {
        if d != c {
            assert(names_wf(pre[d].space, pre[d].generation, lists, d));
        }
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS implies #[trigger] holds_id(post, lists, d, s) == holds_id(pre, lists, d, s) by {
        assert(post[d].generation == pre[d].generation);
    }
    assert forall|d: int| 0 <= d < NUM_CPUS implies {
        &&& 1 <= (#[trigger] post[d]).generation <= ID_GENERATION_MAX
        &&& 1 <= post[d].next_pcid <= PCID_MAX
    } by {
        assert(pre[d].generation == post[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && lists.contains_key(s) implies #[trigger] id_generation(lists[s].value().ids@[d]) <= post[d].generation by {
        assert(id_generation(lists[s].value().ids@[d]) <= pre[d].generation);
    }
    assert forall|d: int, s: usize| 0 <= d < NUM_CPUS && #[trigger] holds_id(post, lists, d, s) implies {
        &&& 1 <= id_pcid(lists[s].value().ids@[d])
        &&& id_pcid(lists[s].value().ids@[d]) < post[d].next_pcid
    } by {
        assert(holds_id(pre, lists, d, s));
    }
    assert forall|d: int, s: usize, r: usize| 0 <= d < NUM_CPUS && s != r && #[trigger] holds_id(post, lists, d, s) && #[trigger] holds_id(post, lists, d, r)
        implies id_pcid(lists[s].value().ids@[d]) != id_pcid(lists[r].value().ids@[d]) by {
        assert(holds_id(pre, lists, d, s));
        assert(holds_id(pre, lists, d, r));
    }
}

/// Something a core may hold in its TLB or paging-structure caches: an entry of this space's tables
/// leading to this page, which is a frame's page or the base page of a table's block.
pub ghost struct TlbEntry {
    pub space: usize,
    pub page: usize,
}

/// Page g is one a TLB entry may name: a page of a typed large block, or the base page of a small
/// block typed as a frame or a table page, which are what a space's tables lead to. A free page is none
/// of these, nor is a member page or a block typed as anything else, so a block can return to free only
/// once no core or IOMMU holds an entry naming any of its pages: see CapKernel::lemma_untranslatable_clean.
pub open spec fn translatable(blocks: &BlockTable, g: usize) -> bool {
    &&& blocks.tracks(g as int)
    &&& (blocks.covered(g as int) || {
        &&& blocks.pages@[g as int].kind is Base
        &&& (blocks.pages@[g as int].object is Frame || blocks.pages@[g as int].object is TablePage)
    })
}

/// Every entry a core or an IOMMU may hold names a page a TLB entry may name.
pub open spec fn entries_translatable(blocks: &BlockTable, tlb: TlbModel, iotlb: IotlbModel) -> bool {
    &&& forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] tlb[c].contains(e) ==> translatable(blocks, e.page)
    &&& forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] iotlb[i].contains(e) ==> translatable(blocks, e.page)
}

/// A step that changes the block table but keeps every page a TLB entry may name keeps the TLB models'
/// entries nameable.
/// A change of one block's count and dead flag keeps every page's kind, object and typed region, so a
/// page a core may translate stays one it may translate.
pub proof fn lemma_refs_changed_translatable(a: &BlockTable, b: &BlockTable, br: BlockRef, refs: usize, dead: bool)
    requires
        blocks_refs_changed(a, b, br, refs, dead),
    ensures
        forall|g: usize| translatable(a, g) ==> #[trigger] translatable(b, g),
{
    assert forall|g: usize| translatable(a, g) implies #[trigger] translatable(b, g) by {
        let i = g as int;
        a.lemma_tracked_regions(i);
        assert(b.pages@[i].kind == a.pages@[i].kind);
        assert(b.regions_2m@[region_2m(i)].typed == a.regions_2m@[region_2m(i)].typed);
        assert(b.regions_1g@[region_1g(i)].typed == a.regions_1g@[region_1g(i)].typed);
    }
}

/// The same, for a change whose block and counts a specification names only inside its own bindings.
pub proof fn lemma_some_refs_changed_translatable(a: &BlockTable, b: &BlockTable)
    requires
        exists|br: BlockRef, refs: usize, dead: bool| #[trigger] blocks_refs_changed(a, b, br, refs, dead),
    ensures
        forall|g: usize| translatable(a, g) ==> #[trigger] translatable(b, g),
{
    let (br, refs, dead) = choose|br: BlockRef, refs: usize, dead: bool| #[trigger] blocks_refs_changed(a, b, br, refs, dead);
    lemma_refs_changed_translatable(a, b, br, refs, dead);
}

/// Typing a free small block keeps every page a core may translate one it may translate: a page of the
/// block was free and in no typed region, so it was none.
pub proof fn lemma_small_typed_translatable(pre: &BlockTable, post: &BlockTable, page: usize, order: usize)
    requires
        small_order(order),
        page % (order_pages(order) as usize) == 0,
        forall|k: int| 0 <= k < order_pages(order) ==> #[trigger] pre.pages@[page + k].kind is Free,
        !pre.covered(page as int),
        post.regions_2m@ == pre.regions_2m@,
        post.regions_1g@ == pre.regions_1g@,
        forall|i: int| pre.tracks(i) && !(page <= i < page + order_pages(order)) ==> #[trigger] post.pages@[i] == pre.pages@[i],
    ensures
        forall|g: usize| translatable(pre, g) ==> #[trigger] translatable(post, g),
{
    assert forall|g: usize| translatable(pre, g) implies #[trigger] translatable(post, g) by {
        if page <= g < page + order_pages(order) {
            assert(pre.pages@[page + (g - page)].kind is Free);
            lemma_small_range_uncovered(pre, page, order, g);
        }
    }
}

pub proof fn lemma_entries_translatable_kept(pre: &BlockTable, post: &BlockTable, tlb: TlbModel, iotlb: IotlbModel)
    requires
        entries_translatable(pre, tlb, iotlb),
        forall|g: usize| translatable(pre, g) ==> #[trigger] translatable(post, g),
    ensures
        entries_translatable(post, tlb, iotlb),
{
    assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] tlb[c].contains(e) implies translatable(post, e.page) by {
        assert(translatable(pre, e.page));
    }
    assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] iotlb[i].contains(e) implies translatable(post, e.page) by {
        assert(translatable(pre, e.page));
    }
}

/// What the kernel needs to send an IOMMU commands, in kernel addresses. Boot fills one for each
/// present IOMMU and programs the ring's base register. The command encoding, the registers and which
/// rings the IOMMU accepts are the arch module's: AMD-Vi on x86_64, SMMUv3 on aarch64.
#[derive(Clone, Copy)]
pub struct CommandBuffer {
    /// The IOMMU's MMIO registers, where CommandBuffers' registers say boot found them.
    pub mmio: usize,
    /// The command ring, `len` commands of arch::IOMMU_COMMAND_SIZE bytes long, page aligned.
    pub ring: usize,
    pub len: usize,
    /// The ring entry the kernel writes next, which the IOMMU's tail or producer register names.
    pub tail: usize,
    /// An 8-byte word outside the ring that the IOMMU stores to when the commands before it are done,
    /// where the arch module's invalidate waits that way: AMD-Vi's COMPLETION_WAIT does.
    pub completion: usize,
}

/// The k-th page of b's ring.
pub open spec fn ring_page(b: CommandBuffer, k: int) -> usize {
    (b.ring + k * PAGE_SZ) as usize
}

/// The page holding b's completion word.
pub open spec fn completion_page(b: CommandBuffer) -> usize {
    (b.completion - b.completion % PAGE_SZ) as usize
}

pub use command_page::CommandPage;

/// A page of an IOMMU's command ring or of its completion word, alone in a module with its
/// permission, so the field is private to it: no code outside can take the permission and write the
/// page through it. The arch module's command glue writes a ring slot by its address and records the
/// command it wrote, so that record is the only way a slot changes, and the IOMMU reads the slot.
mod command_page {
    #[cfg(verus_keep_ghost)]
    use vstd::prelude::*;
    #[cfg(verus_keep_ghost)]
    use crate::define::PagePerm4k;

    // Only specs read the field, and a cargo build erases specs, so only Verus compiles it.
    pub tracked struct CommandPage {
        #[cfg(verus_keep_ghost)]
        tracked perm: PagePerm4k,
    }

    impl CommandPage {
        /// The page's address.
        pub closed spec fn addr(self) -> usize {
            self.perm.addr()
        }
    }
}

pub use iommu_registers::IommuRegisters;

/// An IOMMU's MMIO registers as boot found and programmed them: which IOMMU, the base of its
/// registers, and the command ring boot wrote into its ring base register, by the ring's address and
/// its length in commands. The IOMMU fetches commands from that ring and no other: AMD-Vi's head and
/// tail are offsets from the command buffer base address register, within ComLen (48882 §3.4.1,
/// §3.4.15), and an SMMUv3's indexes are into the queue SMMU_CMDQ_BASE names, of 2^LOG2SIZE entries
/// (IHI 0070 3.5, 6.3.26). Alone in a module, so its fields are private to it: no code outside can
/// make one or change what it says, so one names a register block and a ring only because boot handed
/// it over, and the IOMMU it names keeps it from standing for another IOMMU's. The arch module's
/// command glue loads and stores those registers and writes that ring.
mod iommu_registers {
    #[cfg(verus_keep_ghost)]
    use vstd::prelude::*;

    // Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
    pub tracked struct IommuRegisters {
        #[cfg(verus_keep_ghost)]
        ghost iommu: int,
        #[cfg(verus_keep_ghost)]
        ghost base: usize,
        #[cfg(verus_keep_ghost)]
        ghost ring: usize,
        #[cfg(verus_keep_ghost)]
        ghost len: usize,
    }

    impl IommuRegisters {
        /// The IOMMU, by its index among the present ones.
        pub closed spec fn iommu(self) -> int {
            self.iommu
        }

        /// The address of its MMIO registers.
        pub closed spec fn base(self) -> usize {
            self.base
        }

        /// The address of the command ring boot programmed into its ring base register.
        pub closed spec fn ring(self) -> usize {
            self.ring
        }

        /// The ring's length in commands, as boot programmed it.
        pub closed spec fn len(self) -> usize {
            self.len
        }
    }
}

/// Each IOMMU's command buffer and the pages its ring and completion word sit in. Holding those pages
/// keeps them out of every block the capability kernel hands out, keying them by IOMMU keeps two
/// IOMMUs from sharing one, and holding each as a CommandPage keeps every write of a ring slot in the
/// arch module's command glue. Each IOMMU's registers, keyed by IOMMU, fix where its buffer's mmio
/// points, so the glue loads and stores that IOMMU's registers and no other address, and fix its
/// buffer's ring and length, so the glue writes commands into the ring that IOMMU fetches from.
pub struct CommandBuffers {
    pub buffers: Array<CommandBuffer, NUM_IOMMUS>,
    pub pages: Tracked<Map<(int, usize), CommandPage>>,
    pub registers: Tracked<Map<int, IommuRegisters>>,
}

impl CommandBuffers {
    /// IOMMU i's pages include the one at address a.
    pub open spec fn holds(&self, i: int, a: usize) -> bool {
        &&& self.pages@.contains_key((i, a))
        &&& self.pages@[(i, a)].addr() == a
    }

    /// IOMMU i's ring has a length and a place the IOMMU accepts, its tail is inside it, its ring
    /// and completion word are in pages it holds, its mmio is where boot found i's registers, and its
    /// ring and length are the ones boot programmed into i's ring base register, the ring i fetches
    /// from. The
    /// completion word is 8-byte aligned, as COMPLETION_WAIT's store address is (48882 §2.4.1).
    pub open spec fn buffer_wf(&self, i: int) -> bool {
        let b = self.buffers@[i];
        &&& crate::arch::command_ring_ok(b.ring, b.len)
        &&& b.tail < b.len
        &&& self.registers@.contains_key(i)
        &&& self.registers@[i].iommu() == i
        &&& self.registers@[i].base() == b.mmio
        &&& self.registers@[i].ring() == b.ring
        &&& self.registers@[i].len() == b.len
        &&& b.mmio % crate::arch::IOMMU_MMIO_ALIGN == 0
        &&& b.ring % PAGE_SZ == 0
        &&& b.ring + b.len * crate::arch::IOMMU_COMMAND_SIZE <= usize::MAX
        &&& forall|k: int| 0 <= k < b.len * crate::arch::IOMMU_COMMAND_SIZE / PAGE_SZ as int ==> #[trigger] self.holds(i, ring_page(b, k))
        &&& b.completion % 8 == 0
        &&& !(b.ring <= b.completion < b.ring + b.len * crate::arch::IOMMU_COMMAND_SIZE)
        &&& self.holds(i, completion_page(b))
    }

    /// Every present IOMMU's command buffer is well formed. Opaque, since no step but the command
    /// glue changes a buffer, and every other step's proof is cheaper without its quantifiers.
    #[verifier::opaque]
    pub open spec fn wf(&self, present: Seq<bool>) -> bool {
        &&& self.buffers.wf()
        &&& forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] present[i] ==> self.buffer_wf(i)
    }

    /// Invalidates all of present IOMMU i's caches and waits for it to finish, as the arch module's
    /// invalidate_iommu_all does, which empties i's set in `iotlb`, and moves i's tail past the commands
    /// that wrote. The wait is one unit.
    pub fn invalidate(&mut self, Ghost(present): Ghost<Seq<bool>>, i: usize, Tracked(iotlb): Tracked<&mut IotlbModel>, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(present),
            i < NUM_IOMMUS,
            present[i as int],
        ensures
            final(steps).count <= old(steps).count + 1,
            final(self).wf(present),
            final(self).pages == old(self).pages,
            final(iotlb).len() == old(iotlb).len(),
            final(iotlb)[i as int] == Set::<TlbEntry>::empty(),
            forall|j: int| j != i ==> #[trigger] final(iotlb)[j] == old(iotlb)[j],
    {
        proof {
            reveal(CommandBuffers::wf);
        }
        let ghost pre = *old(self);
        let next = invalidate_iommu_all(self, i, Tracked(iotlb), Tracked(steps));
        let b = *self.buffers.get(i);
        self.buffers.set(i, CommandBuffer { mmio: b.mmio, ring: b.ring, len: b.len, tail: next, completion: b.completion });
        proof {
            reveal(CommandBuffers::wf);
            assert forall|j: int| 0 <= j < NUM_IOMMUS && #[trigger] present[j] implies self.buffer_wf(j) by {
                assert(pre.buffer_wf(j));
                let b = self.buffers@[j];
                assert forall|k: int| 0 <= k < b.len * crate::arch::IOMMU_COMMAND_SIZE / PAGE_SZ as int implies #[trigger] self.holds(j, ring_page(b, k)) by {
                    assert(pre.holds(j, ring_page(pre.buffers@[j], k)));
                }
            }
        }
    }
}

/// For each IOMMU, whether the machine has it, the epoch its last finished invalidate started at, and
/// what it may still hold that its device spaces' tables no longer say, as an IotlbModel that only the
/// invalidate glue empties. A device keeps translating while the kernel runs, so an IOMMU may refill
/// from an entry between an invalidate and that entry's unmap. An absent IOMMU holds nothing and is
/// never invalidated, so the stale check skips it. A present one takes commands through its command
/// buffer.
pub struct IommuState {
    pub present: Array<bool, NUM_IOMMUS>,
    pub acked: Array<usize, NUM_IOMMUS>,
    pub tlb: Tracked<IotlbModel>,
    pub commands: CommandBuffers,
}

impl IommuState {
    /// No IOMMU has acknowledged anything.
    pub fn zero(&mut self)
        requires
            old(self).acked.wf(),
        ensures
            final(self).acked.wf(),
            forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] final(self).acked@[i] == 0,
    {
        let mut i = 0;
        while i != NUM_IOMMUS
            invariant
                0 <= i <= NUM_IOMMUS,
                self.acked.wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.acked@[j] == 0,
            decreases NUM_IOMMUS - i,
        {
            self.acked.set(i, 0);
            i = i + 1;
        }
    }
}

/// When each page's, 2M region's and 1G region's last unmap was, zero if it has none: unmap bumps the
/// epoch first, so a real one is never zero. A block's stale epoch is the word at its level. An unmap
/// writes all three for its page, so a free reads one word however large its block. These outlive a
/// block's typing, so retype cannot lose them.
pub struct StaleEpochs {
    pub pages: Array<usize, NUM_PAGES>,
    pub two: Array<usize, NUM_2M>,
    pub one: Array<usize, NUM_1G>,
}

impl StaleEpochs {
    pub open spec fn wf(&self) -> bool {
        &&& self.pages.wf()
        &&& self.two.wf()
        &&& self.one.wf()
    }

    /// No page's last unmap is later than this epoch.
    pub open spec fn bounded(&self, epoch: int) -> bool {
        forall|g: int| 0 <= g < NUM_PAGES ==> #[trigger] self.pages@[g] <= epoch
    }

    /// A core at epoch `acked` has not acknowledged this page's last unmap, read at any level.
    pub open spec fn above(&self, acked: int, page: usize) -> bool {
        &&& acked < self.pages@[page as int]
        &&& acked < self.two@[(page / PAGES_PER_2M) as int]
        &&& acked < self.one@[(page / PAGES_PER_1G) as int]
    }

    /// This page's unmap happened at this epoch, read at any level.
    pub open spec fn written(&self, epoch: usize, page: usize) -> bool {
        &&& self.pages@[page as int] == epoch
        &&& self.two@[(page / PAGES_PER_2M) as int] == epoch
        &&& self.one@[(page / PAGES_PER_1G) as int] == epoch
    }

    /// The stale word of region r.
    pub open spec fn region(&self, level: Large, r: usize) -> usize {
        match level {
            Large::Two => self.two@[r as int],
            Large::One => self.one@[r as int],
        }
    }

    /// Every word zero: no unmap yet.
    pub fn zero(&mut self)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            forall|j: int| 0 <= j < NUM_PAGES ==> #[trigger] final(self).pages@[j] == 0,
            forall|r: int| 0 <= r < NUM_2M ==> #[trigger] final(self).two@[r] == 0,
            forall|r: int| 0 <= r < NUM_1G ==> #[trigger] final(self).one@[r] == 0,
    {
        let mut i = 0;
        while i != NUM_PAGES
            invariant
                0 <= i <= NUM_PAGES,
                self.wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.pages@[j] == 0,
            decreases NUM_PAGES - i,
        {
            self.pages.set(i, 0);
            i = i + 1;
        }
        let mut i = 0;
        while i != NUM_2M
            invariant
                0 <= i <= NUM_2M,
                self.wf(),
                forall|j: int| 0 <= j < NUM_PAGES ==> #[trigger] self.pages@[j] == 0,
                forall|r: int| 0 <= r < i ==> #[trigger] self.two@[r] == 0,
            decreases NUM_2M - i,
        {
            self.two.set(i, 0);
            i = i + 1;
        }
        let mut i = 0;
        while i != NUM_1G
            invariant
                0 <= i <= NUM_1G,
                self.wf(),
                forall|j: int| 0 <= j < NUM_PAGES ==> #[trigger] self.pages@[j] == 0,
                forall|r: int| 0 <= r < NUM_2M ==> #[trigger] self.two@[r] == 0,
                forall|r: int| 0 <= r < i ==> #[trigger] self.one@[r] == 0,
            decreases NUM_1G - i,
        {
            self.one.set(i, 0);
            i = i + 1;
        }
    }

    /// This run of pages, at most a 2M region's, was unmapped at this epoch. A page above an
    /// acknowledgement older than the epoch stays above it, and a page outside the run keeps its word.
    pub fn record_run(&mut self, first: usize, count: usize, epoch: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            first + count <= NUM_PAGES,
            count <= PAGES_PER_2M,
        ensures
            final(steps).count <= old(steps).count + count,
            final(self).wf(),
            forall|g: usize| first <= g < first + count ==> #[trigger] final(self).written(epoch, g),
            forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) ==> #[trigger] final(self).above(a, g),
            forall|g: int| 0 <= g < NUM_PAGES && !(first <= g < first + count)
                ==> #[trigger] final(self).pages@[g] == old(self).pages@[g],
            forall|e: int| epoch <= e && #[trigger] old(self).bounded(e) ==> final(self).bounded(e),
    {
        let mut k = 0;
        let ghost start = steps.count;
        while k != count
            invariant
                self.wf(),
                0 <= k <= count,
                count <= PAGES_PER_2M,
                steps.count == start + k,
                first + count <= NUM_PAGES,
                forall|g: usize| first <= g < first + k ==> #[trigger] self.written(epoch, g),
                forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) ==> #[trigger] self.above(a, g),
                forall|g: int| 0 <= g < NUM_PAGES && !(first <= g < first + count) ==> #[trigger] self.pages@[g] == old(self).pages@[g],
                forall|e: int| epoch <= e && #[trigger] old(self).bounded(e) ==> self.bounded(e),
            decreases count - k,
        {
            let ghost mid = *self;
            self.record(first + k, epoch);
            proof {
                steps.step();
                let page = (first + k) as usize;
                assert forall|g: usize| first <= g < first + k + 1 implies #[trigger] self.written(epoch, g) by {
                    if g != page {
                        assert(mid.written(epoch, g));
                    }
                }
                assert forall|a: int, g: usize| a < epoch && g < NUM_PAGES && old(self).above(a, g) implies #[trigger] self.above(a, g) by {
                    assert(mid.above(a, g));
                }
                assert forall|e: int| epoch <= e && #[trigger] old(self).bounded(e) implies self.bounded(e) by {
                    assert(mid.bounded(e));
                    assert forall|g: int| 0 <= g < NUM_PAGES implies #[trigger] self.pages@[g] <= e by {
                        if g != page as int {
                            assert(mid.pages@[g] <= e);
                        }
                    }
                }
            }
            k = k + 1;
        }
    }

    /// This page's unmap happened at this epoch.
    pub fn record(&mut self, page: usize, epoch: usize)
        requires
            old(self).wf(),
            page < NUM_PAGES,
        ensures
            final(self).wf(),
            final(self).pages@ == old(self).pages@.update(page as int, epoch),
            final(self).two@ == old(self).two@.update((page / PAGES_PER_2M) as int, epoch),
            final(self).one@ == old(self).one@.update((page / PAGES_PER_1G) as int, epoch),
    {
        self.pages.set(page, epoch);
        self.two.set(page / PAGES_PER_2M, epoch);
        self.one.set(page / PAGES_PER_1G, epoch);
    }
}

/// Every core running nothing, at generation 1 with no PCID handed out, its base register naming no space.
fn init_cores(cores: &mut Array<CoreState, NUM_CPUS>)
    requires
        old(cores).wf(),
    ensures
        final(cores).wf(),
        forall|c: int| 0 <= c < NUM_CPUS ==> {
            &&& (#[trigger] final(cores)@[c]).current_thread is None
            &&& final(cores)@[c].acked_epoch == 0
            &&& final(cores)@[c].generation == 1
            &&& final(cores)@[c].next_pcid == 1
            &&& final(cores)@[c].space is None
        },
{
    let mut i = 0;
    while i != NUM_CPUS
        invariant
            0 <= i <= NUM_CPUS,
            cores.wf(),
            forall|c: int| 0 <= c < i ==> {
                &&& (#[trigger] cores@[c]).current_thread is None
                &&& cores@[c].acked_epoch == 0
                &&& cores@[c].generation == 1
                &&& cores@[c].next_pcid == 1
                &&& cores@[c].space is None
            },
        decreases NUM_CPUS - i,
    {
        cores.set(i, CoreState { current_thread: None, acked_epoch: 0, generation: 1, next_pcid: 1, space: None });
        i = i + 1;
    }
}

pub struct CapKernel {
    pub list: Tree,
    pub cores: Array<CoreState, NUM_CPUS>,
    pub flush_epoch: usize,
    /// For each core, what it may still hold that its space's tables no longer say. What they do say,
    /// a core that loaded the space may hold too: see core_may_hold. Only a flush of a core empties its
    /// set: TlbModel.
    pub tlb: Tracked<TlbModel>,
    pub iommus: IommuState,
    /// Frames some address space maps.
    pub mapped: Ghost<Set<usize>>,
    pub blocks: BlockTable,
    pub tables: Tables,
    pub stale_epoch: StaleEpochs,
    /// The permission of each page of a frame, by page number.
    pub frames: Tracked<Map<usize, PagePerm4k>>,
    /// The table pages' tables and spare pages.
    pub table_pages: TablePages,
    /// The spaces, each a root table named by capabilities.
    pub spaces: Spaces,
    /// What each live mapping node stands for.
    pub mappings: Ghost<IMap<usize, MappingRecord>>,
    /// The large blocks being zeroed. Each is typed with no capability yet.
    pub zeroing: Zeroing,
    /// The frame capabilities holding each block's references.
    pub holders: Ghost<IMap<BlockRef, Set<usize>>>,
    /// The devices boot found.
    pub devices: Devices,
    /// The threads, each a record named by capabilities.
    pub threads: Threads,
    /// The processes, each a record named by capabilities, beside its table's root and its space.
    pub processes: Processes,
    /// The endpoints and notifications, each a record named by capabilities.
    pub endpoints: Endpoints,
    /// The replies, each a record named by capabilities.
    pub replies: Replies,
    /// The cores sent an IPI to act on a pending stop, in the order sent. The send is ghost: see
    /// design/one-lock-bounded-steps/.
    pub stop_ipis: Ghost<Seq<usize>>,
    /// The cores sent an IPI to flush after an unmap, in the order sent: each core on the unmapped
    /// space's list of cores. The send is ghost: see design/flush-without-waiting/.
    pub flush_ipis: Ghost<Seq<usize>>,
    /// The cores sent an IPI to run the selection now, in the order sent: each core a start made a
    /// thread Runnable on that outranks what the core runs. The send is ghost, as the stop IPIs':
    /// see design/cpu-time-as-capability/.
    pub resched_ipis: Ghost<Seq<usize>>,
}

/// A live hidden node is node 0 of a table leaf or a table page, so unlinking it can find what it
/// stands for. A leaf whose hidden node has gone stays in its root entry, refused by lookup, until its
/// own retype frees it. See design/teardown-driven-by-retype/.
pub open spec fn hidden_nodes_are_leaves(list: &Tree, tables: &Tables, pages: &TablePages) -> bool {
    forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Hidden
        ==> tables.owner@.contains_key(n) || pages.maps@.contains_key(n)
}

/// Node i of node page k of table page t.
pub open spec fn table_node(t: usize, k: usize, i: usize) -> usize {
    (table_node_page(t, k) + i) as usize
}

/// A live node in a table page's node pages, other than its hidden node, is a mapping node, so an empty
/// entry's node is free for a map.
pub open spec fn table_nodes_are_mappings(list: &Tree, pages: &TablePages) -> bool {
    forall|t: usize, k: usize, i: usize| #![trigger table_node(t, k, i)]
        pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES && i < NODES_PER_PAGE && (k != 0 || i != 0)
            && list.nodes@[table_node(t, k, i) as int].live
            ==> list.nodes@[table_node(t, k, i) as int].kind is Mapping
}

/// A device space's node pages hold no live node: a mapping's node sits in its own table page's node pages,
/// and a root maps no frame. A process space has no node pages.
pub open spec fn space_nodes_dead(list: &Tree, spaces: &Spaces) -> bool {
    forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
        spaces.roots@.contains_key(s) && !(spaces.records@[s].value().kind is Process) && k < TABLE_NODE_PAGES
            && i < NODES_PER_PAGE
            ==> !list.nodes@[table_node(s, k, i) as int].live
}

/// Only a capability has children, and the list's first node is one, so a hidden node is below
/// something and has nothing below it, and a retype naming its block can unlink it.
pub open spec fn parents_are_capabilities(list: &Tree) -> bool {
    &&& list.nodes@[list.seq@[0] as int].kind is Capability
    &&& forall|x: usize| #[trigger] list.seq@.contains(x) && x != list.seq@[0]
        ==> list.nodes@[list.parent@[x] as int].kind is Capability
}

/// The parents stay capabilities while the list, the parent map and every node in a page the list
/// held are as they were: a live node is in such a page.
pub proof fn lemma_parents_same_live(pre: Tree, post: Tree)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        post.seq == pre.seq,
        post.parent == pre.parent,
        forall|i: usize| #[trigger] pre.valid(i) ==> post.nodes@[i as int] == pre.nodes@[i as int],
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    pre.lemma_live_valid(s[0]);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x;
        pre.lemma_link(k);
        pre.lemma_parent_live(x);
        pre.lemma_live_valid(pre.parent@[x]);
    }
}

/// The parents after a child joins under a capability: the child's parent is one, and no other
/// node's kind or parent changed.
pub proof fn lemma_parents_derived(pre: Tree, post: Tree, c: usize, slot: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        c < NODE_SPACE,
        pre.nodes@[c as int].live,
        pre.nodes@[c as int].kind is Capability,
        slot < NODE_SPACE,
        !pre.nodes@[slot as int].live,
        post.parent@ == pre.parent@.insert(slot, c),
        post.seq@[0] == pre.seq@[0],
        forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != slot ==> {
            &&& post.nodes@[i].live == pre.nodes@[i].live
            &&& post.nodes@[i].kind == pre.nodes@[i].kind
        },
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    assert(s[0] != slot);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        post.lemma_link(k);
        if x != slot {
            assert(pre.nodes@[x as int].live);
            lemma_has(s, x);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
            assert(j != 0);
            assert(pre.parent@.contains_key(s[j]));
            pre.lemma_parent_live(x);
            assert(pre.parent@[x] != slot);
            assert(post.parent@[x] == pre.parent@[x]);
        }
    }
}

/// The parents after a node goes: no parent changed, and a node still listed has a live parent, so
/// not the one that went.
pub proof fn lemma_parents_removed(pre: Tree, post: Tree, i: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        i < NODE_SPACE,
        !post.nodes@[i as int].live,
        post.parent@ == pre.parent@,
        post.seq@[0] == pre.seq@[0],
        forall|x: int| 0 <= x < NODE_SPACE && x != i ==> #[trigger] post.nodes@[x].live == pre.nodes@[x].live,
        forall|x: int| 0 <= x < NODE_SPACE && x != i ==> #[trigger] post.nodes@[x].kind == pre.nodes@[x].kind,
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    pre.lemma_link(0);
    post.lemma_link(0);
    assert(post.seq@[0] != i);
    assert forall|x: usize| #[trigger] post.seq@.contains(x) && x != post.seq@[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < post.seq@.len() && post.seq@[k] == x;
        post.lemma_link(k);
        assert(x != i);
        assert(pre.nodes@[x as int].live);
        lemma_has(s, x);
        assert(k != 0);
        assert(post.parent@.contains_key(post.seq@[k]));
        post.lemma_parent_live(x);
        assert(post.parent@[x] != i);
        assert(pre.nodes@[pre.parent@[x] as int].kind is Capability);
    }
}

/// The parents after capability i is renamed slot: slot's parent is i's, a child of i has slot, and
/// every other parent is as it was.
pub proof fn lemma_parents_moved(pre: Tree, post: Tree, i: usize, slot: usize)
    requires
        pre.wf(),
        post.wf(),
        parents_are_capabilities(&pre),
        i < NODE_SPACE,
        slot < NODE_SPACE,
        i != slot,
        pre.nodes@[i as int].live,
        pre.nodes@[i as int].kind is Capability,
        !pre.nodes@[slot as int].live,
        !post.nodes@[i as int].live,
        post.nodes@[slot as int].kind is Capability,
        exists|p: int| 0 <= p < pre.seq@.len() && #[trigger] pre.seq@[p] == i
            && post.seq@ == pre.seq@.update(p, slot),
        i != pre.seq@[0] ==> post.parent@[slot] == pre.parent@[i],
        forall|x: usize| x != i && x != slot && #[trigger] pre.parent@.contains_key(x) ==>
            post.parent@.contains_key(x) && post.parent@[x] == rename(pre.parent@[x], i, slot),
        forall|x: int| #![trigger post.nodes@[x]] 0 <= x < NODE_SPACE && x != i && x != slot ==> {
            &&& post.nodes@[x].live == pre.nodes@[x].live
            &&& post.nodes@[x].kind == pre.nodes@[x].kind
        },
    ensures
        parents_are_capabilities(&post),
{
    let s = pre.seq@;
    let t = post.seq@;
    let p = choose|p: int| 0 <= p < s.len() && #[trigger] s[p] == i && t == s.update(p, slot);
    pre.lemma_link(0);
    if p == 0 {
        assert(t[0] == slot);
    } else {
        lemma_nodup(s, 0, p);
        assert(t[0] == s[0]);
        assert(s[0] != i && s[0] != slot);
    }
    assert forall|x: usize| #[trigger] t.contains(x) && x != t[0]
        implies post.nodes@[post.parent@[x] as int].kind is Capability by {
        let k = choose|k: int| 0 <= k < t.len() && t[k] == x;
        post.lemma_link(k);
        assert(x != i);
        if x == slot {
            if k != p {
                pre.lemma_link(k);
                assert(t[k] == s[k]);
                assert(false);
            }
            assert(p != 0);
            lemma_nodup(s, 0, p);
            assert(i != s[0]);
            assert(pre.parent@.contains_key(s[p]));
            assert(s.contains(i));
            pre.lemma_parent_live(i);
            assert(pre.d(s[p]) == pre.d(pre.parent@[s[p]]) + 1);
            assert(pre.parent@[i] != i);
            assert(pre.parent@[i] != slot);
            assert(post.parent@[slot] == pre.parent@[i]);
        } else {
            assert(pre.nodes@[x as int].live);
            lemma_has(s, x);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == x;
            assert(j != p);
            assert(t[j] == x);
            if j == 0 {
                assert(p != 0);
                assert(t[0] == x);
                assert(false);
            }
            assert(pre.parent@.contains_key(s[j]));
            assert(post.parent@[x] == rename(pre.parent@[x], i, slot));
            if pre.parent@[x] != i {
                pre.lemma_parent_live(x);
                assert(pre.parent@[x] != slot);
            }
        }
    }
}

/// A live node in a leaf's slot is a capability, since mappings and bindings live in other pages, so
/// tearing down a leaf only ever finds capabilities in it.
pub open spec fn leaf_slots_are_capabilities(list: &Tree, tables: &Tables) -> bool {
    forall|n: usize| #[trigger] list.nodes@[n as int].live && tables.owner@.contains_key(page_of(n))
        && n % PAGE_SZ != 0 && n % PAGE_SZ < NODES_PER_PAGE ==> list.nodes@[n as int].kind is Capability
}

/// The list's first node lives outside every leaf, so whatever a leaf holds can be unlinked.
pub open spec fn first_node_outside_leaves(list: &Tree, tables: &Tables) -> bool {
    !tables.owner@.contains_key(page_of(list.seq@[0]))
}

/// Every capability node but the list's first is in a table's slot, so unlinking it can read what it
/// says.
pub open spec fn capability_nodes_are_slots(list: &Tree, tables: &Tables) -> bool {
    forall|n: usize| n < NODE_SPACE && (#[trigger] list.nodes@[n as int]).live && list.nodes@[n as int].kind is Capability
        && n != list.seq@[0] ==> tables.is_cap(list, n)
}

/// A page the list holds nodes in is not free, so a newly typed block's first page is not already one,
/// and is no block's member, so a leaf's second page is not one and its block can free whole.
pub open spec fn list_pages_used(list: &Tree, blocks: &BlockTable) -> bool {
    forall|p: usize| #[trigger] list.pages@.dom().contains(p) && blocks.tracks_addr(p) ==> {
        &&& !(blocks.pages@[(p / PAGE_SZ) as int].kind is Free)
        &&& blocks.pages@[(p / PAGE_SZ) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(p / PAGE_SZ) as int].base as int].object is TablePage
                || blocks.pages@[blocks.pages@[(p / PAGE_SZ) as int].base as int].object is Space
        &&& !(blocks.pages@[(p / PAGE_SZ) as int].object is Frame)
    }
}

/// The list's pages stay used while no page changes kind or object and every page keeps its block: a
/// member page is in no typed region, so its block names its base.
pub proof fn lemma_list_pages_used_same_kinds(list: &Tree, a: &BlockTable, b: &BlockTable)
    requires
        list_pages_used(list, a),
        a.wf(),
        forall|i: int| a.tracks(i) ==> {
            &&& (#[trigger] b.pages@[i]).kind == a.pages@[i].kind
            &&& b.pages@[i].object == a.pages@[i].object
        },
        forall|i: usize| a.tracks(i as int) ==> #[trigger] block_ref(b, i) == block_ref(a, i),
        forall|x: int| 0 <= x < NUM_2M ==> (#[trigger] b.regions_2m@[x]).typed == a.regions_2m@[x].typed,
        forall|x: int| 0 <= x < NUM_1G ==> (#[trigger] b.regions_1g@[x]).typed == a.regions_1g@[x].typed,
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && b.tracks_addr(p) implies {
        &&& !(b.pages@[(p / PAGE_SZ) as int].kind is Free)
        &&& b.pages@[(p / PAGE_SZ) as int].kind is Member
            ==> b.pages@[b.pages@[(p / PAGE_SZ) as int].base as int].object is TablePage
                || b.pages@[b.pages@[(p / PAGE_SZ) as int].base as int].object is Space
        &&& !(b.pages@[(p / PAGE_SZ) as int].object is Frame)
    } by {
        let x = p / PAGE_SZ;
        assert(b.pages@[x as int].kind == a.pages@[x as int].kind);
        if a.pages@[x as int].kind is Member {
            a.lemma_not_free_uncovered(x as int);
            a.lemma_member(x as int);
            assert(block_ref(a, x) == BlockRef::Small(a.pages@[x as int].base));
            assert(block_ref(b, x) == BlockRef::Small(b.pages@[x as int].base));
            assert(b.pages@[x as int].base == a.pages@[x as int].base);
        }
    }
}

/// Each block being zeroed is a live typed region of the block table. It is what keeps a newly typed
/// region, whose pages were not covered, apart from every block being zeroed.
pub open spec fn zeroing_typed(z: &Zeroing, blocks: &BlockTable) -> bool {
    forall|b: usize| #[trigger] z.blocks@.contains_key(b) ==> {
        &&& z.blocks@[b] == PAGES_PER_2M ==> {
            &&& blocks.regions_2m@[(b / PAGES_PER_2M) as int].typed
            &&& !blocks.regions_2m@[(b / PAGES_PER_2M) as int].dead
        }
        &&& z.blocks@[b] == PAGES_PER_1G ==> {
            &&& blocks.regions_1g@[(b / PAGES_PER_1G) as int].typed
            &&& !blocks.regions_1g@[(b / PAGES_PER_1G) as int].dead
        }
    }
}

impl CapKernel {
    pub open spec fn acked(&self, c: int) -> int {
        self.cores@[c].acked_epoch as int
    }

    /// The epoch IOMMU i's last finished invalidate started at.
    pub open spec fn iommu_acked(&self, i: int) -> int {
        self.iommus.acked@[i] as int
    }

    /// The machine has IOMMU i.
    pub open spec fn iommu_present(&self, i: int) -> bool {
        self.iommus.present@[i]
    }

    /// Core c has loaded space s.
    pub open spec fn loaded(&self, c: int, s: usize) -> bool {
        &&& self.spaces.loaded@.contains_key(s)
        &&& core_listed(self.spaces.loaded@[s].value().list, c)
    }

    /// Core c has acknowledged the flush that retired space s. The retire ran while no core's base
    /// register named s, none can name it until a load clears the retire, and a load would have cleared
    /// it, so c holds nothing of s and cannot walk it. See design/teardown-driven-by-retype/.
    pub open spec fn past_retire(&self, c: int, s: usize) -> bool {
        &&& self.spaces.loaded@.contains_key(s)
        &&& self.spaces.loaded@[s].value().retired != 0
        &&& self.spaces.loaded@[s].value().retired <= self.acked(c)
    }

    /// Core c may hold or walk an entry of space s: it loaded s and is not past s's retire.
    pub open spec fn depends(&self, c: int, s: usize) -> bool {
        &&& self.loaded(c, s)
        &&& !self.past_retire(c, s)
    }

    /// A core depends on the space its base register names, and that space holds a valid id on the core,
    /// so the tag the register was written under is still that space's alone.
    pub proof fn lemma_named_depends(&self, c: int, s: usize)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
            self.cores@[c].space == Some(s),
        ensures
            self.loaded(c, s),
            self.spaces.loaded@[s].value().retired == 0,
            self.depends(c, s),
            holds_id(self.cores@, self.spaces.loaded@, c, s),
    {
        reveal(ids_wf);
        assert(names_wf(self.cores@[c].space, self.cores@[c].generation, self.spaces.loaded@, c));
    }

    /// A core on a space's list has loaded a space, so one that has not holds no entry of any space.
    pub proof fn lemma_loaded_a_space(&self, c: int)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
        ensures
            forall|s: usize| #[trigger] self.loaded(c, s) ==> has_loaded(self.cores@[c]),
            forall|e: TlbEntry| #[trigger] self.tlb@[c].contains(e) ==> has_loaded(self.cores@[c]),
    {
        reveal(ids_wf);
        assert forall|e: TlbEntry| #[trigger] self.tlb@[c].contains(e) implies has_loaded(self.cores@[c]) by {
            assert(self.depends(c, e.space));
            assert(self.loaded(c, e.space));
        }
    }

    /// A core holds an entry of a space only if it depends on the space. A translation to an unmapped page
    /// can survive on a core only if that core has not yet acknowledged the page's unmap. The strict
    /// comparison needs unmap to bump the epoch first, and no unmap is recorded later than the epoch, so
    /// a core that has acknowledged it holds nothing stale. A core holds entries only under PCIDs it has
    /// handed out. The same holds of each IOMMU.
    pub open spec fn tlb_wf(&self) -> bool {
        &&& self.tlb@.len() == NUM_CPUS
        &&& tags_wf(self.cores@, self.tlb@)
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] self.acked(c) <= self.flush_epoch
        &&& self.stale_epoch.bounded(self.flush_epoch as int)
        &&& forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) ==> self.depends(c, e.space)
        &&& forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) && !self.mapped@.contains(e.page)
            ==> self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.acked(c), e.page)
        &&& self.iommus_wf()
    }

    /// A translation to an unmapped page can survive in an IOMMU only if it has not yet acknowledged the
    /// page's unmap. An absent IOMMU holds nothing.
    pub open spec fn iommus_wf(&self) -> bool {
        &&& self.iommus.present.wf()
        &&& self.iommus.acked.wf()
        &&& self.iommus.tlb@.len() == NUM_IOMMUS
        &&& self.iommus.commands.wf(self.iommus.present@)
        &&& forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) ==> self.iommu_present(i)
        &&& forall|i: int| 0 <= i < NUM_IOMMUS ==> #[trigger] self.iommu_acked(i) <= self.flush_epoch
        &&& forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] self.iommus.tlb@[i].contains(e) && !self.mapped@.contains(e.page)
            ==> self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.iommu_acked(i), e.page)
    }

    /// The IOMMU model reads nothing but itself, the epoch and the staleness record; of the command
    /// buffers it reads only that they are well formed, and a rise of the epoch keeps it.
    pub proof fn lemma_iommus_same(pre: Self, post: Self)
        requires
            pre.iommus_wf(),
            post.iommus.present == pre.iommus.present,
            post.iommus.acked == pre.iommus.acked,
            post.iommus.tlb == pre.iommus.tlb,
            post.iommus.commands.wf(post.iommus.present@),
            pre.flush_epoch <= post.flush_epoch,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
        ensures
            post.iommus_wf(),
    {
        assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) implies post.iommu_present(i) by {
            assert(pre.iommus.tlb@[i].contains(e));
        }
        assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] post.iommu_acked(i) <= post.flush_epoch by {
            assert(pre.iommu_acked(i) <= pre.flush_epoch);
        }
        assert forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.iommu_acked(i), e.page) by {
            assert(pre.iommus.tlb@[i].contains(e));
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.list.wf()
        &&& self.cores.wf()
        &&& self.blocks.wf()
        &&& self.tables.wf(&self.list)
        &&& self.tables.caps_wf(&self.list)
        &&& self.tables.control_wf(&self.list)
        &&& self.stale_epoch.wf()
        &&& self.tlb_wf()
        &&& entries_translatable(&self.blocks, self.tlb@, self.iommus.tlb@)
        &&& ids_wf(self.cores@, self.spaces.loaded@)
        &&& registers_wf(self.spaces.registers@, self.cores@, self.spaces.loaded@, self.spaces.kernel_root@)
        &&& kernel_root_reserved(&self.blocks, self.spaces.kernel_root@)
        &&& self.frames_wf()
        &&& self.zeroing.wf()
        &&& zeroing_typed(&self.zeroing, &self.blocks)
        &&& list_pages_used(&self.list, &self.blocks)
        &&& hidden_nodes_are_leaves(&self.list, &self.tables, &self.table_pages)
        &&& table_nodes_are_mappings(&self.list, &self.table_pages)
        &&& space_nodes_dead(&self.list, &self.spaces)
        &&& table_pages_wf(&self.list, &self.table_pages, &self.blocks)
        &&& spaces_wf(&self.list, &self.tables, &self.spaces, &self.blocks)
        &&& threads_wf(&self.list, &self.tables, &self.threads, &self.blocks)
        &&& processes_wf(&self.list, &self.tables, &self.processes, &self.blocks)
        &&& endpoints_wf(&self.list, &self.tables, &self.endpoints, &self.blocks)
        &&& replies_wf(&self.list, &self.tables, &self.replies, &self.blocks)
        &&& process_tables_wf(&self.tables, &self.processes)
        &&& process_spaces_wf(&self.spaces, &self.processes)
        &&& current_wf(self.cores@, self.threads.records@)
        &&& placed_running_wf(self.threads.records@)
        &&& queues_wf(&self.threads.queues, self.threads.records@)
        &&& waits_wf(self.endpoints.records@, self.threads.records@)
        &&& bindings_wf(&self.list, &self.threads, &self.processes)
        &&& binding_parents(&self.list, &self.tables, &self.threads)
        &&& placements_wf(&self.list, &self.tables, &self.threads)
        &&& table_links_wf(tree_of(&self.table_pages, &self.spaces))
        &&& mapped_wf(self.mapped@, self.mappings@)
        &&& mappings_wf(&self.list, &self.tables, tree_of(&self.table_pages, &self.spaces), &self.blocks, self.holders@, self.mappings@)
        &&& capability_nodes_are_slots(&self.list, &self.tables)
        &&& parents_are_capabilities(&self.list)
        &&& badges_inherited(&self.list, &self.tables)
        &&& first_node_outside_leaves(&self.list, &self.tables)
        &&& leaf_slots_are_capabilities(&self.list, &self.tables)
        &&& holders_wf(&self.list, &self.tables, &self.blocks, &self.zeroing, self.holders@)
        &&& objects_wf(&self.tables, &self.blocks, self.holders@)
        &&& frames_held(self.frames@, self.holders@)
        &&& leaf_blocks_wf(&self.list, &self.tables, &self.blocks)
        &&& devices_wf(&self.list, &self.tables, &self.devices)
        &&& device_bindings_wf(&self.list, &self.tables, self.spaces.bound@, &self.devices)
        &&& devices_placed(&self.list, self.iommus.present@, self.iommus.acked@, &self.devices)
        &&& !self.threads.records@.contains_key(self.devices.page)
    }

    /// One thread's record is well formed. A caller that needs only this keeps wf hidden: revealed,
    /// wf brings the block table's counts and their set ranges into every later query.
    pub proof fn lemma_thread_wf(&self, t: usize)
        requires
            self.wf(),
            self.threads.records@.contains_key(t),
        ensures
            thread_wf(&self.list, &self.threads, &self.blocks, t),
    {
    }

    /// One space's record is well formed, without revealing wf: see lemma_thread_wf.
    pub proof fn lemma_space_wf(&self, s: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
        ensures
            space_wf(&self.list, &self.spaces, &self.blocks, s),
    {
    }

    /// Each process has its space, without revealing wf: see lemma_thread_wf.
    pub proof fn lemma_process_spaces_wf(&self)
        requires
            self.wf(),
        ensures
            process_spaces_wf(&self.spaces, &self.processes),
    {
    }

    /// A frame's permission is for its own page.
    pub open spec fn frames_wf(&self) -> bool {
        forall|i: usize| #[trigger] self.frames@.contains_key(i) ==> self.frames@[i].addr() == i * PAGE_SZ
    }

    /// No core or IOMMU can reach page f, a frame's or a table's, through something stale, under any
    /// space. What retype needs, as a fact it can check: see lemma_acknowledged_is_clean.
    pub open spec fn no_stale_translation(&self, f: usize) -> bool {
        &&& forall|c: int, s: usize| 0 <= c < NUM_CPUS ==> !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: f })
        &&& forall|i: int, s: usize| 0 <= i < NUM_IOMMUS ==> !#[trigger] self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f })
    }

    /// A page no TLB entry may name has no stale translation, so neither has any page of a block about
    /// to free whose type is neither frame nor table page, nor a member page of any small block.
    pub proof fn lemma_untranslatable_clean(&self, f: usize)
        requires
            self.wf(),
            !translatable(&self.blocks, f),
        ensures
            self.no_stale_translation(f),
    {
        assert forall|c: int, s: usize| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: f }) by {
            if self.tlb@[c].contains(TlbEntry { space: s, page: f }) {
                assert(translatable(&self.blocks, TlbEntry { space: s, page: f }.page));
            }
        }
        assert forall|i: int, s: usize| 0 <= i < NUM_IOMMUS implies !#[trigger] self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) by {
            if self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) {
                assert(translatable(&self.blocks, TlbEntry { space: s, page: f }.page));
            }
        }
    }

    /// A step that frees the large block that is region r of this level, keeping the TLB models, keeps
    /// their entries nameable when no core or IOMMU holds an entry for any page of the block.
    pub proof fn lemma_large_freed_translatable(pre: Self, post: &BlockTable, level: Large, r: usize)
        requires
            pre.wf(),
            r < level_regions(level),
            pre.region_clean(level, r),
            post.pages@ == pre.blocks.pages@,
            match level {
                Large::Two => {
                    &&& post.regions_2m@ == pre.blocks.regions_2m@.update(r as int, post.regions_2m@[r as int])
                    &&& post.regions_1g@ == pre.blocks.regions_1g@
                },
                Large::One => {
                    &&& post.regions_1g@ == pre.blocks.regions_1g@.update(r as int, post.regions_1g@[r as int])
                    &&& post.regions_2m@ == pre.blocks.regions_2m@
                },
            },
        ensures
            entries_translatable(post, pre.tlb@, pre.iommus.tlb@),
    {
        assert forall|g: usize| translatable(&pre.blocks, g) && !block_has_page(level_ref(level, r), g)
            implies #[trigger] translatable(post, g) by {
            match level {
                Large::Two => assert(region_2m(g as int) != r as int),
                Large::One => assert(region_1g(g as int) != r as int),
            }
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.tlb@[c].contains(e) implies translatable(post, e.page) by {
            assert(translatable(&pre.blocks, e.page));
            if block_has_page(level_ref(level, r), e.page) {
                assert(pre.no_stale_translation(e.page));
                assert(TlbEntry { space: e.space, page: e.page } == e);
            }
        }
        assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) implies translatable(post, e.page) by {
            assert(translatable(&pre.blocks, e.page));
            if block_has_page(level_ref(level, r), e.page) {
                assert(pre.no_stale_translation(e.page));
                assert(TlbEntry { space: e.space, page: e.page } == e);
            }
        }
    }

    /// A page of the small block at base other than the base is a member, outside every typed large
    /// block, so no TLB entry may name it.
    pub proof fn lemma_in_freed_block_untranslatable(pre: Self, base: usize, g: usize)
        requires
            pre.wf(),
            pre.blocks.tracks(base as int),
            pre.blocks.pages@[base as int].kind is Base,
            pre.blocks.in_block(base as int, g as int),
            translatable(&pre.blocks, g),
        ensures
            g == base,
    {
        if g != base {
            pre.blocks.lemma_member_of(base as int, g as int);
            pre.blocks.lemma_not_free_uncovered(g as int);
        }
    }

    /// A step that frees the small block at base, keeping the TLB models, keeps their entries nameable
    /// when no core or IOMMU holds an entry for the base page: a member page and a block typed as
    /// neither frame nor table page hold none.
    pub proof fn lemma_small_freed_translatable(pre: Self, post: &BlockTable, base: usize)
        requires
            pre.wf(),
            pre.blocks.tracks(base as int),
            pre.blocks.pages@[base as int].kind is Base,
            pre.no_stale_translation(base),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.pages@[i] == (
                if pre.blocks.in_block(base as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.regions_2m@ == pre.blocks.regions_2m@,
            post.regions_1g@ == pre.blocks.regions_1g@,
        ensures
            entries_translatable(post, pre.tlb@, pre.iommus.tlb@),
    {
        assert forall|g: usize| translatable(&pre.blocks, g) && !pre.blocks.in_block(base as int, g as int)
            implies #[trigger] translatable(post, g) by {
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] pre.tlb@[c].contains(e) implies translatable(post, e.page) by {
            assert(translatable(&pre.blocks, e.page));
            if pre.blocks.in_block(base as int, e.page as int) {
                Self::lemma_in_freed_block_untranslatable(pre, base, e.page);
                assert(TlbEntry { space: e.space, page: base } == e);
            }
        }
        assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] pre.iommus.tlb@[i].contains(e) implies translatable(post, e.page) by {
            assert(translatable(&pre.blocks, e.page));
            if pre.blocks.in_block(base as int, e.page as int) {
                Self::lemma_in_freed_block_untranslatable(pre, base, e.page);
                assert(TlbEntry { space: e.space, page: base } == e);
            }
        }
    }

    /// Every core that has loaded a space and every present IOMMU has acknowledged this epoch. A core
    /// that has not loaded one holds no translation of any space (lemma_loaded_a_space), an absent IOMMU
    /// holds none either, and neither is sent a flush, so neither has anything to acknowledge. Either
    /// kind of space may have mapped a page, and the word records only when.
    /// See design/flush-without-waiting/.
    pub open spec fn all_acknowledged(&self, epoch: int) -> bool {
        &&& forall|c: int| 0 <= c < NUM_CPUS && has_loaded(self.cores@[c]) ==> epoch <= #[trigger] self.acked(c)
        &&& forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] self.iommu_present(i) ==> epoch <= self.iommu_acked(i)
    }

    /// Something can hold a translation: a core has loaded a space, or an IOMMU is present. An unmap
    /// then leaves its pages unacknowledged; with neither, nothing holds a translation of any space
    /// and no acknowledgement is waited for.
    pub open spec fn flush_awaited(&self) -> bool {
        ||| exists|c: int| 0 <= c < NUM_CPUS && has_loaded(#[trigger] self.cores@[c])
        ||| exists|i: int| 0 <= i < NUM_IOMMUS && #[trigger] self.iommu_present(i)
    }

    /// A page whose word was written past the epoch `pre` stood at, by a step that left every
    /// acknowledgement as it was, is unacknowledged while anything can hold a translation.
    pub proof fn lemma_unmap_unacknowledged(pre: Self, post: Self, f: usize)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus.acked == pre.iommus.acked,
            pre.flush_epoch < post.stale_epoch.pages@[f as int],
            post.flush_awaited(),
        ensures
            !post.acknowledged(f),
    {
        let epoch = post.stale_epoch.pages@[f as int] as int;
        if exists|c: int| 0 <= c < NUM_CPUS && has_loaded(#[trigger] post.cores@[c]) {
            let c = choose|c: int| 0 <= c < NUM_CPUS && has_loaded(#[trigger] post.cores@[c]);
            assert(pre.acked(c) <= pre.flush_epoch);
            assert(post.acked(c) < epoch);
        } else {
            let i = choose|i: int| 0 <= i < NUM_IOMMUS && #[trigger] post.iommu_present(i);
            assert(pre.iommu_acked(i) <= pre.flush_epoch);
            assert(post.iommu_acked(i) < epoch);
        }
    }

    /// Every core and IOMMU has acknowledged f's last unmap.
    pub open spec fn acknowledged(&self, f: usize) -> bool {
        &&& self.blocks.tracks(f as int)
        &&& self.all_acknowledged(self.stale_epoch.pages@[f as int] as int)
    }

    /// Every core and IOMMU has acknowledged the last unmap of any page of region r.
    pub open spec fn region_acknowledged(&self, level: Large, r: usize) -> bool {
        self.all_acknowledged(self.stale_epoch.region(level, r) as int)
    }

    /// No page of region r is mapped.
    pub open spec fn region_unmapped(&self, level: Large, r: usize) -> bool {
        forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> !self.mapped@.contains(i)
    }

    /// No core or IOMMU can reach any page of region r through something stale.
    pub open spec fn region_clean(&self, level: Large, r: usize) -> bool {
        forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) ==> self.no_stale_translation(i)
    }

    /// The rule the cross-CPU proofs rest on: a step by core c leaves every other core's current
    /// thread alone.
    pub open spec fn writes_only_own_current(pre: Self, post: Self, c: int) -> bool {
        forall|d: int| 0 <= d < NUM_CPUS && d != c
            ==> #[trigger] post.cores@[d].current_thread == pre.cores@[d].current_thread
    }

    /// What every step by core c must establish.
    pub open spec fn step_ok(pre: Self, post: Self, c: int) -> bool {
        &&& post.wf()
        &&& Self::writes_only_own_current(pre, post, c)
    }

    /// A valid id is one this core has handed out, and nothing is under a PCID it has not.
    pub proof fn lemma_id_handed_out(&self, c: int, s: usize, p: usize)
        requires
            self.wf(),
            0 <= c < NUM_CPUS,
        ensures
            holds_id(self.cores@, self.spaces.loaded@, c, s) ==> {
                &&& 1 <= id_pcid(self.spaces.loaded@[s].value().ids@[c])
                &&& id_pcid(self.spaces.loaded@[s].value().ids@[c]) < self.cores@[c].next_pcid
            },
            self.cores@[c].next_pcid <= p ==> !self.tlb@.tags(c).contains(p),
            1 <= self.cores@[c].generation <= ID_GENERATION_MAX,
            1 <= self.cores@[c].next_pcid <= PCID_MAX,
    {
        reveal(ids_wf);
        assert(1 <= self.cores@[c].generation <= ID_GENERATION_MAX);
    }

    /// Only core c's state and its model of the TLB changed, and it stays on what it was running.
    pub open spec fn only_core_changed(pre: Self, post: Self, c: int) -> bool {
        &&& post.list == pre.list
        &&& post.tables == pre.tables
        &&& post.blocks == pre.blocks
        &&& post.holders == pre.holders
        &&& post.mappings == pre.mappings
        &&& post.table_pages == pre.table_pages
        &&& post.zeroing == pre.zeroing
        &&& post.frames == pre.frames
        &&& post.spaces == pre.spaces
        &&& post.mapped == pre.mapped
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.iommus == pre.iommus
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
        &&& post.cores@[c].current_thread == pre.cores@[c].current_thread
        &&& post.cores@[c].space == pre.cores@[c].space
        &&& pre.acked(c) <= post.acked(c)
        &&& forall|e: TlbEntry| #[trigger] post.tlb@[c].contains(e) ==> pre.tlb@[c].contains(e)
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.cores@[d] == pre.cores@[d]
        &&& forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] post.tlb@[d] == pre.tlb@[d]
    }

    /// Only IOMMU i's acknowledgement, its model of the IOTLB and the IOMMUs' command buffers changed.
    pub open spec fn only_iommu_changed(pre: Self, post: Self, i: int) -> bool {
        &&& post.list == pre.list
        &&& post.cores == pre.cores
        &&& post.flush_epoch == pre.flush_epoch
        &&& post.tlb == pre.tlb
        &&& post.mapped == pre.mapped
        &&& post.blocks == pre.blocks
        &&& post.tables == pre.tables
        &&& post.stale_epoch == pre.stale_epoch
        &&& post.frames == pre.frames
        &&& post.table_pages == pre.table_pages
        &&& post.spaces == pre.spaces
        &&& post.mappings == pre.mappings
        &&& post.zeroing == pre.zeroing
        &&& post.holders == pre.holders
        &&& post.devices == pre.devices
        &&& post.threads == pre.threads
        &&& post.processes == pre.processes
        &&& post.endpoints == pre.endpoints
        &&& post.replies == pre.replies
        &&& post.stop_ipis == pre.stop_ipis
        &&& post.flush_ipis == pre.flush_ipis
        &&& post.iommus.present == pre.iommus.present
        &&& forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] post.iommu_acked(j) == pre.iommu_acked(j)
        &&& forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] post.iommus.tlb@[j] == pre.iommus.tlb@[j]
    }

    /// A step that changed only core c, and not the space its register names, keeps the registers.
    pub proof fn lemma_registers_core(pre: Self, post: Self, c: int)
        requires
            pre.wf(),
            0 <= c < NUM_CPUS,
            Self::only_core_changed(pre, post, c),
        ensures
            registers_wf(post.spaces.registers@, post.cores@, post.spaces.loaded@, post.spaces.kernel_root@),
    {
        assert forall|d: int| 0 <= d < NUM_CPUS implies (#[trigger] post.cores@[d]).space == pre.cores@[d].space by {
            if d != c {
                assert(post.cores@[d] == pre.cores@[d]);
            }
        }
        lemma_registers_kept(pre.spaces.registers@, pre.cores@, post.cores@, pre.spaces.loaded@, post.spaces.loaded@, pre.spaces.kernel_root@);
    }

    /// An unmapped page every core and IOMMU has acknowledged is free of stale translations.
    pub proof fn lemma_acknowledged_is_clean(&self, f: usize)
        requires
            self.wf(),
            !self.mapped@.contains(f),
            self.acknowledged(f),
        ensures
            self.no_stale_translation(f),
    {
        assert forall|c: int, s: usize| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: f }) by {
            if self.tlb@[c].contains(TlbEntry { space: s, page: f }) {
                self.lemma_loaded_a_space(c);
                assert(self.stale_epoch.above(self.acked(c), f));
                assert(self.stale_epoch.pages@[f as int] <= self.acked(c));
            }
        }
        assert forall|i: int, s: usize| 0 <= i < NUM_IOMMUS implies !#[trigger] self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) by {
            if self.iommus.tlb@[i].contains(TlbEntry { space: s, page: f }) {
                assert(self.iommu_present(i));
                assert(self.stale_epoch.above(self.iommu_acked(i), f));
                assert(self.stale_epoch.pages@[f as int] <= self.iommu_acked(i));
            }
        }
    }

    /// A step that leaves the stale epochs, the cores and the IOMMUs as they were leaves every page
    /// acknowledged that was.
    pub proof fn lemma_acknowledged_kept(pre: Self, post: Self, f: usize)
        requires
            post.stale_epoch == pre.stale_epoch,
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            pre.acknowledged(f),
        ensures
            post.acknowledged(f),
    {
        let epoch = pre.stale_epoch.pages@[f as int] as int;
        assert forall|c: int| 0 <= c < NUM_CPUS && has_loaded(post.cores@[c]) implies epoch <= #[trigger] post.acked(c) by {
            assert(pre.acked(c) == post.acked(c));
        }
        assert forall|i: int| 0 <= i < NUM_IOMMUS && #[trigger] post.iommu_present(i) implies epoch <= post.iommu_acked(i) by {
            assert(pre.iommu_present(i) && pre.iommu_acked(i) == post.iommu_acked(i));
        }
    }

    /// A region with no page mapped, every core and IOMMU having acknowledged its word, is free of stale
    /// translations on every page: each page's unmap wrote that word too.
    pub proof fn lemma_region_acknowledged_is_clean(&self, level: Large, r: usize)
        requires
            self.wf(),
            self.region_unmapped(level, r),
            self.region_acknowledged(level, r),
        ensures
            self.region_clean(level, r),
    {
        assert forall|i: usize| #[trigger] block_has_page(level_ref(level, r), i) implies self.no_stale_translation(i) by {
            assert(i / level_pages(level) == r) by {
                match level {
                    Large::Two => {
                        assert(r * PAGES_PER_2M <= i < (r + 1) * PAGES_PER_2M);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            i as int, PAGES_PER_2M as int, r as int, i - r * PAGES_PER_2M);
                    },
                    Large::One => {
                        assert(r * PAGES_PER_1G <= i < (r + 1) * PAGES_PER_1G);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                            i as int, PAGES_PER_1G as int, r as int, i - r * PAGES_PER_1G);
                    },
                }
            }
            assert forall|c: int, s: usize| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(TlbEntry { space: s, page: i }) by {
                if self.tlb@[c].contains(TlbEntry { space: s, page: i }) {
                    self.lemma_loaded_a_space(c);
                    assert(!self.mapped@.contains(i));
                    assert(self.stale_epoch.above(self.acked(c), i));
                    assert(self.stale_epoch.region(level, r) <= self.acked(c));
                }
            }
            assert forall|j: int, s: usize| 0 <= j < NUM_IOMMUS implies !#[trigger] self.iommus.tlb@[j].contains(TlbEntry { space: s, page: i }) by {
                if self.iommus.tlb@[j].contains(TlbEntry { space: s, page: i }) {
                    assert(self.iommu_present(j));
                    assert(!self.mapped@.contains(i));
                    assert(self.stale_epoch.above(self.iommu_acked(j), i));
                    assert(self.stale_epoch.region(level, r) <= self.iommu_acked(j));
                }
            }
        }
    }

    /// Makes this a kernel with one root capability, no mappings, no core running anything or naming a space and each at generation 1, every page
    /// Reserved with no unmap recorded, and the IOMMUs boot found present with their command buffers.
    /// `registers` are the cores' base registers as boot left them, each naming `kernel_root` under
    /// KERNEL_TAG, `tlb` is the cores' TLB model as boot makes it, each core's sets empty, and `iotlb` the
    /// IOMMUs', each IOMMU's set empty. In place,
    /// since the block table is too large to move by value.
    pub(crate) fn init(
        &mut self,
        root: usize,
        Tracked(perm): Tracked<PointsTo<NodePage>>,
        kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>,
        iommus_present: Array<bool, NUM_IOMMUS>,
        iommu_commands: CommandBuffers,
        kernel_root: usize,
        Tracked(registers): Tracked<Map<int, BaseRegister>>,
        Tracked(tlb): Tracked<TlbModel>,
        Tracked(iotlb): Tracked<IotlbModel>,
    )
        requires
            boot_registers(registers, kernel_root),
            boot_tlb(tlb),
            boot_iotlb(iotlb),
            root % PAGE_SZ == 0,
            root + PAGE_SZ <= NODE_SPACE,
            perm.addr() == root,
            perm.is_init(),
            perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
            kernel_entries.wf(),
            iommus_present.wf(),
            iommu_commands.wf(iommus_present@),
        ensures
            final(self).wf(),
            final(self).spaces.kernel_entries == kernel_entries,
            final(self).iommus.present == iommus_present,
            final(self).iommus.commands == iommu_commands,
            final(self).flush_epoch == 0,
            final(self).spaces.kernel_root@ == kernel_root,
            final(self).spaces.registers@ == registers,
            final(self).mapped@ == Set::<usize>::empty(),
            final(self).devices.count == 0,
            forall|c: int| 0 <= c < NUM_CPUS ==> {
                &&& (#[trigger] final(self).cores@[c]).current_thread is None
                &&& final(self).cores@[c].generation == 1
                &&& final(self).cores@[c].next_pcid == 1
                &&& final(self).cores@[c].space is None
            },
            final(self).list.seq@[0] == root,
            final(self).boot_empty(),
            forall|j: int| final(self).blocks.tracks(j) ==> #[trigger] final(self).stale_epoch.pages@[j] == 0,
            forall|r: int| 0 <= r < NUM_2M ==> #[trigger] final(self).stale_epoch.two@[r] == 0,
            forall|r: int| 0 <= r < NUM_1G ==> #[trigger] final(self).stale_epoch.one@[r] == 0,
    {
        reveal(table_links_wf);
        self.list = Tree::new(root, Tracked(perm));
        self.tables = Tables::new();
        self.table_pages = TablePages::new();
        self.spaces = Spaces::new(kernel_entries, kernel_root, Tracked(registers));
        self.mappings = Ghost(IMap::empty());
        self.frames = Tracked(Map::tracked_empty());
        // Boot holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        self.zeroing.cursor.init();
        self.zeroing.active_2m.init();
        self.zeroing.active_1g.init();
        self.zeroing.init(Tracked(&mut steps));
        self.holders = Ghost(IMap::empty());
        self.devices = Devices::new(root);
        self.threads.init(Tracked(&mut steps));
        self.processes = Processes::new();
        self.endpoints = Endpoints::new();
        self.replies = Replies::new();
        self.blocks.pages.init();
        self.blocks.regions_2m.init();
        self.blocks.regions_1g.init();
        self.blocks.count_2m.init();
        self.blocks.count_1g.init();
        self.blocks.init(Tracked(&mut steps));
        self.cores.init();
        init_cores(&mut self.cores);
        self.stale_epoch.pages.init();
        self.stale_epoch.two.init();
        self.stale_epoch.one.init();
        self.stale_epoch.zero();
        self.iommus.acked.init();
        self.iommus.zero();
        self.iommus.tlb = Tracked(iotlb);
        self.iommus.present = iommus_present;
        self.iommus.commands = iommu_commands;
        proof {
            assert forall|n: usize| n < NODE_SPACE && (#[trigger] self.list.nodes@[n as int]).live
                && self.list.nodes@[n as int].kind is Hidden implies self.tables.owner@.contains_key(n) by {
                assert(n == root);
            }
        }
        self.flush_epoch = 0;
        self.tlb = Tracked(tlb);
        self.mapped = Ghost(Set::empty());
        proof {
            reveal(ids_wf);
            reveal(registers_wf);
            reveal(devices_wf);
            reveal(current_wf);
            reveal(placed_running_wf);
            reveal(binding_parents);
            reveal(placements_wf);
            reveal(device_bindings_wf);
            reveal(badges_inherited);
            lemma_waits_empty();
            assert(self.endpoints.records@ == Map::<usize, PointsTo<QueueRecord>>::empty());
            assert(self.threads.records@ == Map::<usize, PointsTo<ThreadRecord>>::empty());
            assert forall|c: int, t: usize| 0 <= c < NUM_CPUS && #[trigger] runs(self.cores@, c, t) implies false by {
                assert(self.cores@[c].current_thread is None);
            }
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] names_wf(self.cores@[c].space, self.cores@[c].generation, self.spaces.loaded@, c) by {
                assert(self.cores@[c].space is None);
            }
        }
    }

    /// A step that does nothing keeps the invariant, the shape every later step is stated in.
    pub fn no_op(&self, c: usize)
        requires
            self.wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*self, *self, c as int),
    {
    }

    /// Whether every core and IOMMU has acknowledged f's last unmap, which is a bounded number of loads.
    pub fn is_acknowledged(&self, f: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            self.blocks.tracks(f as int),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + NUM_IOMMUS,
            ret == self.acknowledged(f),
    {
        self.has_acknowledged(*self.stale_epoch.pages.get(f), Tracked(steps))
    }

    /// Whether every core and IOMMU has acknowledged the last unmap of any page of region r.
    pub fn is_region_acknowledged(&self, level: Large, r: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
            r < level_regions(level),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + NUM_IOMMUS,
            ret == self.region_acknowledged(level, r),
    {
        let epoch = match level {
            Large::Two => *self.stale_epoch.two.get(r),
            Large::One => *self.stale_epoch.one.get(r),
        };
        self.has_acknowledged(epoch, Tracked(steps))
    }

    /// Whether every core that has loaded a space and every present IOMMU has reached this epoch, which
    /// is a bounded number of loads.
    fn has_acknowledged(&self, epoch: usize, Tracked(steps): Tracked<&mut Steps>) -> (ret: bool)
        requires
            self.wf(),
        ensures
            final(steps).count <= old(steps).count + NUM_CPUS + NUM_IOMMUS,
            ret == self.all_acknowledged(epoch as int),
    {
        let mut c = 0;
        let ghost start = steps.count;
        while c != NUM_CPUS
            invariant
                self.wf(),
                0 <= c <= NUM_CPUS,
                steps.count == start + c,
                start == old(steps).count,
                forall|d: int| 0 <= d < c && has_loaded(self.cores@[d]) ==> epoch <= #[trigger] self.acked(d),
            decreases NUM_CPUS - c,
        {
            let state = self.cores.get(c);
            if state.loaded_a_space() && state.acked_epoch < epoch {
                assert(has_loaded(self.cores@[c as int]));
                assert(self.acked(c as int) < epoch);
                return false;
            }
            c = c + 1;
            proof {
                steps.step();
            }
        }
        let mut i = 0;
        while i != NUM_IOMMUS
            invariant
                self.wf(),
                0 <= i <= NUM_IOMMUS,
                steps.count == start + NUM_CPUS + i,
                start == old(steps).count,
                forall|d: int| 0 <= d < NUM_CPUS && has_loaded(self.cores@[d]) ==> epoch <= #[trigger] self.acked(d),
                forall|j: int| 0 <= j < i && #[trigger] self.iommu_present(j) ==> epoch <= self.iommu_acked(j),
            decreases NUM_IOMMUS - i,
        {
            if *self.iommus.present.get(i) && *self.iommus.acked.get(i) < epoch {
                assert(self.iommu_present(i as int));
                assert(self.iommu_acked(i as int) < epoch);
                return false;
            }
            i = i + 1;
            proof {
                steps.step();
            }
        }
        true
    }

    /// The TLB model reads nothing but the cores, the epoch, the staleness record and the core lists it
    /// has entries for.
    pub proof fn lemma_tlb_same(pre: Self, post: Self)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            forall|s: usize| #[trigger] pre.spaces.loaded@.contains_key(s) ==> {
                &&& post.spaces.loaded@.contains_key(s)
                &&& post.spaces.loaded@[s].value() == pre.spaces.loaded@[s].value()
            },
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.depends(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.spaces.loaded@.contains_key(e.space));
            assert(pre.depends(c, e.space));
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.acked(c) == post.acked(c));
        }
        Self::lemma_iommus_same(pre, post);
    }

    /// The TLB model after a space no core loaded goes: no core held an entry of it.
    pub proof fn lemma_tlb_space_removed(pre: Self, post: Self, base: usize)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.spaces.loaded@ == pre.spaces.loaded@.remove(base),
            forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && e.space == base ==> !#[trigger] pre.tlb@[c].contains(e),
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.depends(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
            assert(e.space != base);
            assert(pre.spaces.loaded@.contains_key(e.space));
            assert(post.spaces.loaded@[e.space] == pre.spaces.loaded@[e.space]);
            assert(pre.depends(c, e.space));
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.acked(c) == post.acked(c));
        }
        Self::lemma_iommus_same(pre, post);
    }

    /// More pages being mapped keeps the TLB model: it says least about a mapped page.
    pub proof fn lemma_tlb_more_mapped(pre: Self, post: Self)
        requires
            pre.tlb_wf(),
            post.cores == pre.cores,
            post.iommus == pre.iommus,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            forall|g: usize| #[trigger] pre.mapped@.contains(g) ==> post.mapped@.contains(g),
            post.stale_epoch == pre.stale_epoch,
            post.spaces.loaded == pre.spaces.loaded,
        ensures
            post.tlb_wf(),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.acked(c) <= post.flush_epoch by {
            assert(pre.acked(c) <= pre.flush_epoch);
        }
        assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) implies post.depends(c, e.space) by {
            assert(pre.tlb@[c].contains(e));
            assert(pre.depends(c, e.space));
        }
        assert forall|c: int, e: TlbEntry|
            0 <= c < NUM_CPUS && #[trigger] post.tlb@[c].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.acked(c), e.page) by {
            assert(pre.tlb@[c].contains(e));
            assert(!pre.mapped@.contains(e.page));
            assert(pre.acked(c) == post.acked(c));
        }
        assert forall|i: int, e: TlbEntry| 0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) implies post.iommu_present(i) by {
            assert(pre.iommus.tlb@[i].contains(e));
        }
        assert forall|i: int| 0 <= i < NUM_IOMMUS implies #[trigger] post.iommu_acked(i) <= post.flush_epoch by {
            assert(pre.iommu_acked(i) <= pre.flush_epoch);
        }
        assert forall|i: int, e: TlbEntry|
            0 <= i < NUM_IOMMUS && #[trigger] post.iommus.tlb@[i].contains(e) && !post.mapped@.contains(e.page)
            implies post.blocks.tracks(e.page as int) && post.stale_epoch.above(post.iommu_acked(i), e.page) by {
            assert(pre.iommus.tlb@[i].contains(e));
            assert(!pre.mapped@.contains(e.page));
        }
    }

    /// The mappings after a step that changed only the blocks and the holders, keeping every typed
    /// block's pages in it and every holder in place, adding none.
    pub proof fn lemma_mappings_blocks_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
        ensures
            mappings_wf(&post.list, &post.tables, tree_of(&post.table_pages, &post.spaces), &post.blocks, post.holders@, post.mappings@),
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n) implies mapping_node_kept(
            &pre.list, &pre.tables, &pre.blocks, pre.holders@, &post.list, &post.tables, &post.blocks, post.holders@, pre.mappings@[n].frame, n,
        ) by {
            pre.lemma_mapping_node(n);
        }
        Self::lemma_mappings_same_tree(pre, post);
    }

    /// Freeing the block at `base` keeps the kernel root's page Reserved: every page of a block is its
    /// base or a member, none Reserved.
    pub proof fn lemma_kernel_root_freed(pre: Self, post: Self, base: int)
        requires
            pre.wf(),
            pre.blocks.tracks(base),
            pre.blocks.pages@[base].kind is Base,
            post.spaces.kernel_root == pre.spaces.kernel_root,
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(base, i) { free_entry() } else { pre.blocks.pages@[i] }),
        ensures
            kernel_root_reserved(&post.blocks, post.spaces.kernel_root@),
    {
        let r = (pre.spaces.kernel_root@ / PAGE_SZ) as int;
        if pre.blocks.tracks(r) && pre.blocks.in_block(base, r) && r != base {
            pre.blocks.lemma_member_of(base, r);
        }
    }

    /// Typing `n` pages from `page` that were Free keeps the kernel root's page Reserved.
    pub proof fn lemma_kernel_root_typed(pre: Self, post: Self, page: int, n: int)
        requires
            pre.wf(),
            post.spaces.kernel_root == pre.spaces.kernel_root,
            forall|k: int| 0 <= k < n ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + n) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            kernel_root_reserved(&post.blocks, post.spaces.kernel_root@),
    {
        let r = (pre.spaces.kernel_root@ / PAGE_SZ) as int;
        if pre.blocks.tracks(r) && page <= r < page + n {
            assert(pre.blocks.pages@[page + (r - page)].kind is Free);
        }
    }

    /// Changing only the `n` pages from `start`, none of them the kernel root's, keeps it Reserved.
    pub proof fn lemma_kernel_root_apart(pre: Self, post: Self, start: int, n: int)
        requires
            pre.wf(),
            post.spaces.kernel_root == pre.spaces.kernel_root,
            kernel_root_apart(&pre.blocks, pre.spaces.kernel_root@, start, n),
            forall|i: int| pre.blocks.tracks(i) && !(start <= i < start + n) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
        ensures
            kernel_root_reserved(&post.blocks, post.spaces.kernel_root@),
    {
        let r = (pre.spaces.kernel_root@ / PAGE_SZ) as int;
        if pre.blocks.tracks(r) {
            assert(post.blocks.pages@[r] == pre.blocks.pages@[r]);
        }
    }

    /// Changing only the block table, the frames and the zeroing table keeps the invariant if each of
    /// them keeps its own, every typed block keeps its pages and every holder stays in place.
    pub proof fn lemma_zeroing_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            kernel_root_reserved(&post.blocks, post.spaces.kernel_root@),
            post.blocks.wf(),
            post.frames_wf(),
            post.zeroing.wf(),
            zeroing_typed(&post.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
            entries_translatable(&post.blocks, post.tlb@, post.iommus.tlb@),
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
        Self::lemma_mappings_blocks_changed(pre, post);
    }

    /// Changing only the block table keeps the invariant.
    pub proof fn lemma_blocks_changed(pre: Self, post: Self)
        requires
            pre.wf(),
            kernel_root_reserved(&post.blocks, post.spaces.kernel_root@),
            post.blocks.wf(),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints || waits_wf(post.endpoints.records@, post.threads.records@),
            post.frames_wf(),
            post.zeroing == pre.zeroing,
            zeroing_typed(&pre.zeroing, &post.blocks),
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            frames_held(post.frames@, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
            endpoints_wf(&post.list, &post.tables, &post.endpoints, &post.blocks),
            replies_wf(&post.list, &post.tables, &post.replies, &post.blocks),
            forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
                && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
                ==> #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i),
            forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
                ==> post.holders@.contains_key(br) && post.holders@[br].contains(n),
            forall|br: BlockRef, n: usize| post.holders@.contains_key(br) && #[trigger] post.holders@[br].contains(n)
                ==> pre.holders@.contains_key(br) && pre.holders@[br].contains(n),
            entries_translatable(&post.blocks, post.tlb@, post.iommus.tlb@),
        ensures
            post.wf(),
    {
        Self::lemma_tlb_same(pre, post);
        Self::lemma_mappings_blocks_changed(pre, post);
    }

    /// A live node in a slot of an owned leaf is a capability.
    pub proof fn lemma_live_slot_is_cap(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            self.tables.owner@.contains_key(page_of(n)),
            n % PAGE_SZ != 0,
            n % PAGE_SZ < NODES_PER_PAGE,
        ensures
            self.is_cap(n),
    {
    }

    /// A node in a leaf's page is not the list's first.
    pub proof fn lemma_leaf_node_not_first(&self, n: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(page_of(n)),
        ensures
            n != self.list.seq@[0],
    {
    }

    /// A live hidden node has a parent and nothing below it.
    pub proof fn lemma_hidden_is_leaf(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Hidden,
        ensures
            n != self.list.seq@[0],
            self.list.childless(n),
    {
        if !self.list.childless(n) {
            self.list.lemma_next_is_child(n);
        }
    }

    /// A live hidden node is an owned leaf's or a table page's, which its block's object tells apart.
    /// That block holds its one reference and is no holder's key.
    pub proof fn lemma_hidden_block(&self, n: usize)
        requires
            self.wf(),
            n < NODE_SPACE,
            self.list.nodes@[n as int].live,
            self.list.nodes@[n as int].kind is Hidden,
        ensures
            self.tables.owner@.contains_key(n) || self.table_pages.maps@.contains_key(n),
            self.blocks.tracks_addr(n),
            self.tables.owner@.contains_key(n) == (self.blocks.pages@[(n / PAGE_SZ) as int].object is TableLeaf),
            self.table_pages.maps@.contains_key(n) == (self.blocks.pages@[(n / PAGE_SZ) as int].object is TablePage),
            block_typed(&self.blocks, BlockRef::Small(n / PAGE_SZ)),
            block_refs(&self.blocks, BlockRef::Small(n / PAGE_SZ)) == 1,
            !block_dead(&self.blocks, BlockRef::Small(n / PAGE_SZ)),
            !self.holders@.contains_key(BlockRef::Small(n / PAGE_SZ)),
    {
        if self.tables.owner@.contains_key(n) {
            lemma_leaf_block_unkeyed(&self.tables, &self.blocks, self.holders@, n);
        } else {
            assert(self.table_pages.maps@.contains_key(n));
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
            lemma_table_page_unkeyed(&self.list, &self.table_pages, &self.tables, &self.blocks, self.holders@, n);
        }
    }

    /// A slot's node is no leaf, since a leaf is page aligned.
    pub proof fn lemma_slot_not_owned(&self, n: usize)
        requires
            self.wf(),
            n % PAGE_SZ != 0,
        ensures
            !self.tables.owner@.contains_key(n),
    {
        if self.tables.owner@.contains_key(n) {
            self.tables.lemma_leaf(&self.list, n);
        }
    }

    /// A live node that is not hidden is no leaf, since a leaf's live node is its hidden one.
    pub proof fn lemma_unhidden_not_owned(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            !(self.list.nodes@[n as int].kind is Hidden),
        ensures
            !self.tables.owner@.contains_key(n),
    {
        if self.tables.owner@.contains_key(n) {
            assert(self.list.nodes@[n as int].kind is Hidden);
        }
    }

    /// A step that changes no node but n and m, neither a leaf, leaves every leaf's node as it was.
    pub proof fn lemma_same_leaf_nodes(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !pre.tables.owner@.contains_key(n),
            !pre.tables.owner@.contains_key(m),
        ensures
            same_leaf_nodes(&pre.list, &post.list, &pre.tables),
            same_leaf_nodes(&pre.list, &post.list, &post.tables),
    {
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(page_of(l) == l);
            pre.lemma_slot_bound(l);
            assert(l != n && l != m);
        }
    }

    /// The kernel after a small block frees, its holder entry going with it, and its record when it is
    /// an endpoint's, a notification's or a reply's. What it still holds of the frames is the caller's
    /// to say, since a frame hands its pages back from there.
    pub proof fn lemma_small_freed(pre: Self, post: Self, base: usize)
        requires
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            queue_object(pre.blocks.pages@[base as int].object) ==> {
                &&& post.endpoints.records@ == pre.endpoints.records@.remove((base * PAGE_SZ) as usize)
                &&& post.endpoints.holders == pre.endpoints.holders
                &&& pre.endpoints.records@[(base * PAGE_SZ) as usize].value().waiters@.len() == 0
            },
            !queue_object(pre.blocks.pages@[base as int].object) ==> post.endpoints == pre.endpoints,
            pre.blocks.pages@[base as int].object is Reply ==> {
                &&& post.replies.records@ == pre.replies.records@.remove((base * PAGE_SZ) as usize)
                &&& post.replies.holders == pre.replies.holders
            },
            !(pre.blocks.pages@[base as int].object is Reply) ==> post.replies == pre.replies,
            pre.wf(),
            pre.blocks.tracks(base as int),
            pre.blocks.pages@[base as int].kind is Base,
            !(pre.blocks.pages@[base as int].object is Process),
            pre.blocks.pages@[base as int].refs == 0,
            pre.no_stale_translation(base),
            post.blocks.wf(),
            forall|i: int| pre.blocks.tracks(i) ==> #[trigger] post.blocks.pages@[i] == (
                if pre.blocks.in_block(base as int, i) { free_entry() } else { pre.blocks.pages@[i] }),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) && pre.blocks.tracks_addr(p)
                ==> !pre.blocks.in_block(base as int, (p / PAGE_SZ) as int),
            post.holders@ == pre.holders@.remove(BlockRef::Small(base)),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames_wf(),
            frames_held(post.frames@, post.holders@),
        ensures
            post.wf(),
    {
        Self::lemma_small_freed_translatable(pre, &post.blocks, base);
        lemma_holders_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, base);
        lemma_list_pages_used_small_freed(&pre.list, &pre.blocks, &post.blocks, base);
        assert forall|t: usize, k: usize| #[trigger] pre.table_pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(table_page_wf(&pre.list, &pre.table_pages, &pre.blocks, t));
        }
        lemma_table_pages_small_freed(&pre.list, &post.list, &pre.table_pages, &pre.blocks, &post.blocks, base);
        assert forall|s: usize, k: usize| #[trigger] pre.spaces.roots@.contains_key(s) && !(pre.spaces.records@[s].value().kind is Process)
            && k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
            assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
        }
        lemma_spaces_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, base);
        assert forall|t: usize| #[trigger] pre.threads.records@.contains_key(t) implies post.list.pages@.dom().contains(t) by {
            assert(thread_wf(&pre.list, &pre.threads, &pre.blocks, t));
        }
        lemma_threads_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, base);
        lemma_processes_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, base);
        if queue_object(pre.blocks.pages@[base as int].object) {
            assert(endpoint_block(&pre.blocks, base));
            assert(pre.endpoints.records@.contains_key((base * PAGE_SZ) as usize));
            lemma_waits_queue_removed(pre.endpoints.records@, pre.threads.records@, (base * PAGE_SZ) as usize);
            lemma_endpoints_own_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &post.endpoints, &pre.blocks, &post.blocks, base);
        } else {
            lemma_endpoints_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.endpoints, &pre.blocks, &post.blocks, base);
        }
        if pre.blocks.pages@[base as int].object is Reply {
            lemma_replies_own_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &post.replies, &pre.blocks, &post.blocks, base);
        } else {
            lemma_replies_small_freed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.replies, &pre.blocks, &post.blocks, base);
        }
        assert forall|x: usize| #[trigger] post.holders@.contains_key(BlockRef::Small(x))
            implies post.blocks.pages@[x as int].object is Frame by {
            assert(x != base);
            assert(pre.holders@.contains_key(BlockRef::Small(x)));
            assert(block_typed(&pre.blocks, BlockRef::Small(x)));
            if pre.blocks.in_block(base as int, x as int) {
                pre.blocks.lemma_base(base as int);
                pre.blocks.lemma_base(x as int);
                if x != base {
                    pre.blocks.lemma_member_of(base as int, x as int);
                }
            }
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
        }
        assert forall|l: usize| #[trigger] post.tables.owner@.contains_key(l) implies {
            &&& post.blocks.tracks_addr(l)
            &&& post.blocks.pages@[(l / PAGE_SZ) as int].kind is Base
            &&& post.blocks.pages@[(l / PAGE_SZ) as int].object is TableLeaf
            &&& post.blocks.pages@[(l / PAGE_SZ) as int].order == 1
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            assert(pre.list.pages@.dom().contains(l));
            assert(!pre.blocks.in_block(base as int, (l / PAGE_SZ) as int));
            assert(post.blocks.pages@[(l / PAGE_SZ) as int] == pre.blocks.pages@[(l / PAGE_SZ) as int]);
        }
        assert forall|x: usize| post.blocks.tracks(x as int) && #[trigger] leaf_block(&post.blocks, x)
            implies post.tables.owner@.contains_key((x * PAGE_SZ) as usize) by {
            assert(!pre.blocks.in_block(base as int, x as int));
            assert(post.blocks.pages@[x as int] == pre.blocks.pages@[x as int]);
            assert(leaf_block(&pre.blocks, x));
        }
        lemma_leaf_blocks_small_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, pre.holders@, base);
        assert forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {
            assert(block_ref(&pre.blocks, i) != BlockRef::Small(base));
            lemma_block_ref_small_freed(&pre.blocks, &post.blocks, base, i);
        }
        assert forall|br: BlockRef, n: usize| pre.holders@.contains_key(br) && #[trigger] pre.holders@[br].contains(n)
            implies post.holders@.contains_key(br) && post.holders@[br].contains(n) by {
            if br == BlockRef::Small(base) {
                assert(pre.holders@[br].len() == 0);
                pre.holders@[br].lemma_len0_is_empty();
            }
        }
        Self::lemma_kernel_root_freed(pre, post, base as int);
        Self::lemma_blocks_changed(pre, post);
    }

    /// The kernel after a dead large block frees, its holder entry going with it. A block being zeroed is
    /// not dead, so it is not this one.
    pub proof fn lemma_large_freed(pre: Self, post: Self, level: Large, r: usize)
        requires
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
            post.endpoints == pre.endpoints,
            post.replies == pre.replies,
            pre.wf(),
            r < level_regions(level),
            pre.region_clean(level, r),
            post.blocks.wf(),
            post.blocks.pages@ == pre.blocks.pages@,
            match level {
                Large::Two => {
                    &&& pre.blocks.regions_2m@[r as int].typed
                    &&& pre.blocks.regions_2m@[r as int].dead
                    &&& pre.blocks.regions_2m@[r as int].refs == 0
                    &&& !post.blocks.regions_2m@[r as int].typed
                    &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@.update(r as int, post.blocks.regions_2m@[r as int])
                    &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@
                },
                Large::One => {
                    &&& pre.blocks.regions_1g@[r as int].typed
                    &&& pre.blocks.regions_1g@[r as int].dead
                    &&& pre.blocks.regions_1g@[r as int].refs == 0
                    &&& !post.blocks.regions_1g@[r as int].typed
                    &&& post.blocks.regions_1g@ == pre.blocks.regions_1g@.update(r as int, post.blocks.regions_1g@[r as int])
                    &&& post.blocks.regions_2m@ == pre.blocks.regions_2m@
                },
            },
            post.holders@ == pre.holders@.remove(level_ref(level, r)),
            post.list == pre.list,
            post.tables == pre.tables,
            post.table_pages == pre.table_pages,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.stale_epoch == pre.stale_epoch,
            post.zeroing == pre.zeroing,
            post.frames_wf(),
            frames_held(post.frames@, post.holders@),
        ensures
            post.wf(),
    {
        Self::lemma_large_freed_translatable(pre, &post.blocks, level, r);
        match level {
            Large::Two => lemma_holders_2m_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, r),
            Large::One => lemma_holders_1g_freed(&pre.list, &pre.tables, &pre.blocks, &post.blocks, &pre.zeroing, pre.holders@, r),
        }
        assert forall|b: usize| #[trigger] pre.zeroing.blocks@.contains_key(b) implies {
            &&& pre.zeroing.blocks@[b] == PAGES_PER_2M ==> {
                &&& post.blocks.regions_2m@[(b / PAGES_PER_2M) as int].typed
                &&& !post.blocks.regions_2m@[(b / PAGES_PER_2M) as int].dead
            }
            &&& pre.zeroing.blocks@[b] == PAGES_PER_1G ==> {
                &&& post.blocks.regions_1g@[(b / PAGES_PER_1G) as int].typed
                &&& !post.blocks.regions_1g@[(b / PAGES_PER_1G) as int].dead
            }
        } by {
            assert(pre.zeroing.block_level(b));
            if pre.zeroing.blocks@[b] == PAGES_PER_2M && level is Two {
                assert((b / PAGES_PER_2M) as int != r as int);
            }
            if pre.zeroing.blocks@[b] == PAGES_PER_1G && level is One {
                assert((b / PAGES_PER_1G) as int != r as int);
            }
        }
        lemma_leaf_blocks_same_pages(&pre.list, &pre.tables, &pre.blocks, &post.blocks);
        lemma_leaf_blocks_owned_same_types(&pre.tables, &pre.blocks, &post.blocks);
        lemma_table_pages_same_pages(&pre.list, &pre.table_pages, &pre.blocks, &post.blocks);
        lemma_spaces_same_pages(&pre.list, &pre.tables, &pre.spaces, &pre.blocks, &post.blocks);
        lemma_threads_same_pages(&pre.list, &pre.tables, &pre.threads, &pre.blocks, &post.blocks);
        lemma_processes_same_pages(&pre.list, &pre.tables, &pre.processes, &pre.blocks, &post.blocks);
        lemma_endpoints_same_pages(&pre.list, &pre.tables, &pre.endpoints, &pre.blocks, &post.blocks);
        lemma_replies_same_pages(&pre.list, &pre.tables, &pre.replies, &pre.blocks, &post.blocks);
        let br = level_ref(level, r);
        assert forall|i: usize| pre.blocks.tracks(i as int) && block_typed(&pre.blocks, block_ref(&pre.blocks, i))
            && block_refs(&pre.blocks, block_ref(&pre.blocks, i)) > 0
            implies #[trigger] block_ref(&post.blocks, i) == block_ref(&pre.blocks, i) by {
            assert(block_ref(&pre.blocks, i) != br);
            match level {
                Large::Two => lemma_block_ref_2m_freed(&pre.blocks, &post.blocks, r, i),
                Large::One => lemma_block_ref_1g_freed(&pre.blocks, &post.blocks, r, i),
            }
        }
        assert forall|k: BlockRef, n: usize| pre.holders@.contains_key(k) && #[trigger] pre.holders@[k].contains(n)
            implies post.holders@.contains_key(k) && post.holders@[k].contains(n) by {
            if k == br {
                assert(pre.holders@[k].len() == 0);
                pre.holders@[k].lemma_len0_is_empty();
            }
        }
        Self::lemma_blocks_changed(pre, post);
    }

    /// Present IOMMU i invalidates all it holds and acknowledges the current epoch. The epoch is read and
    /// the invalidate made here, so no unmap comes between them, and the invalidate is what empties i's
    /// model: design/flush-without-waiting/. The wait for the invalidate is one unit.
    pub fn flush_iommu(&mut self, i: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            i < NUM_IOMMUS,
            old(self).iommu_present(i as int),
        ensures
            final(steps).count <= old(steps).count + FLUSH_IOMMU_STEPS,
            final(self).wf(),
            final(self).iommu_acked(i as int) == old(self).flush_epoch,
            forall|j: int| 0 <= j < NUM_IOMMUS && j != i ==> #[trigger] final(self).iommu_acked(j) == old(self).iommu_acked(j),
            final(self).iommus.tlb@[i as int] == Set::<TlbEntry>::empty(),
            Self::only_iommu_changed(*old(self), *final(self), i as int),
    {
        let ghost pre = *old(self);
        let epoch = self.flush_epoch;
        let ghost present = self.iommus.present@;
        self.iommus.commands.invalidate(Ghost(present), i, Tracked(self.iommus.tlb.borrow_mut()), Tracked(steps));
        self.iommus.acked.set(i, epoch);
        proof {
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] self.acked(c) <= self.flush_epoch by {
                assert(pre.acked(c) <= pre.flush_epoch);
            }
            assert forall|c: int, e: TlbEntry| 0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) implies self.depends(c, e.space) by {
                assert(pre.tlb@[c].contains(e));
                assert(pre.depends(c, e.space));
            }
            assert forall|c: int, e: TlbEntry|
                0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.acked(c), e.page) by {
                assert(pre.tlb@[c].contains(e));
                assert(pre.acked(c) == self.acked(c));
            }
            assert forall|j: int, e: TlbEntry| 0 <= j < NUM_IOMMUS && #[trigger] self.iommus.tlb@[j].contains(e) implies self.iommu_present(j) by {
                assert(j != i as int);
                assert(pre.iommus.tlb@[j].contains(e));
            }
            assert forall|j: int| 0 <= j < NUM_IOMMUS implies #[trigger] self.iommu_acked(j) <= self.flush_epoch by {
                if j != i as int {
                    assert(pre.iommu_acked(j) <= pre.flush_epoch);
                }
            }
            assert forall|j: int, e: TlbEntry|
                0 <= j < NUM_IOMMUS && #[trigger] self.iommus.tlb@[j].contains(e) && !self.mapped@.contains(e.page)
                implies self.blocks.tracks(e.page as int) && self.stale_epoch.above(self.iommu_acked(j), e.page) by {
                assert(j != i as int);
                assert(pre.iommus.tlb@[j].contains(e));
                assert(pre.iommu_acked(j) == self.iommu_acked(j));
            }
            // An acknowledgement only rises, so a bound device's IOMMU still acknowledged its last unbind.
            assert(pre.iommu_acked(i as int) <= pre.flush_epoch);
            assert forall|d: int| 0 <= d < self.devices.count && (#[trigger] self.devices.records@[d]).space is Some implies {
                &&& self.iommus.present@[self.devices.records@[d].iommu as int]
                &&& self.devices.records@[d].unbound <= self.iommus.acked@[self.devices.records@[d].iommu as int]
            } by {
                let j = self.devices.records@[d].iommu as int;
                assert(pre.devices.records@[d].unbound <= pre.iommus.acked@[j]);
                if j != i as int {
                    assert(self.iommus.acked@[j] == pre.iommus.acked@[j]);
                }
            }
        }
    }

    /// Core c flushes every context and acknowledges the current epoch. The flush is made here, so no
    /// register load or user code on c comes between it and the acknowledgement, and the flush is what
    /// empties c's TLB model: design/flush-without-waiting/.
    pub fn acknowledge(&mut self, c: usize, Tracked(steps): Tracked<&mut Steps>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            final(steps).count <= old(steps).count + ACKNOWLEDGE_STEPS,
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).acked(c as int) == old(self).flush_epoch,
            final(self).tlb@[c as int] == Set::<TlbEntry>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).tlb@[d] == old(self).tlb@[d],
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            Self::only_core_changed(*old(self), *final(self), c as int),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).cores@[d] == old(self).cores@[d],
            final(self).cores@[c as int].generation == old(self).cores@[c as int].generation,
            final(self).cores@[c as int].next_pcid == old(self).cores@[c as int].next_pcid,
            final(self).tlb@.tags(c as int) == Set::<usize>::empty(),
            forall|d: int| 0 <= d < NUM_CPUS && d != c ==> #[trigger] final(self).tlb@.tags(d) == old(self).tlb@.tags(d),
    {
        let ghost pre = *old(self);
        let epoch = self.flush_epoch;
        flush_every_context(Tracked(self.tlb.borrow_mut()), c);
        proof {
            assert(pre.acked(c as int) <= pre.flush_epoch);
        }
        let state = *self.cores.get(c);
        self.cores.set(c, CoreState {
            current_thread: state.current_thread,
            acked_epoch: epoch,
            generation: state.generation,
            next_pcid: state.next_pcid,
            space: state.space,
        });
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] self.cores@[d] == pre.cores@[d] by {}
            assert forall|d: int, p: usize| 0 <= d < NUM_CPUS && #[trigger] self.tlb@.tags(d).contains(p) implies p < self.cores@[d].next_pcid by {
                assert(d != c as int);
                assert(pre.tlb@.tags(d).contains(p));
            }
            Self::lemma_registers_core(pre, *self, c as int);
            Self::lemma_iommus_same(pre, *self);
            reveal(ids_wf);
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies #[trigger] self.cores@[d] == pre.cores@[d] by {}
            lemma_ids_core_step(pre.cores@, self.cores@, self.spaces.loaded@, c as int);
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                if d != c as int {
                    assert(self.cores@[d] == pre.cores@[d]);
                    assert(pre.acked(d) <= pre.flush_epoch);
                }
            }
            assert forall|d: int| 0 <= d < NUM_CPUS implies
                #[trigger] self.cores@[d].current_thread == pre.cores@[d].current_thread by {
                if d != c as int {
                    assert(self.cores@[d] == pre.cores@[d]);
                }
            }
            lemma_current_same(pre.cores@, self.cores@, pre.threads.records@, self.threads.records@);
            assert forall|d: int, f: TlbEntry|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(f) && !self.mapped@.contains(f.page)
                implies self.blocks.tracks(f.page as int) && self.stale_epoch.above(self.acked(d), f.page) by {
                if d == c as int {
                    assert(self.tlb@[d] == Set::<TlbEntry>::empty());
                    assert(!self.tlb@[d].contains(f));
                }
                assert(d != c as int);
                assert(self.cores@[d] == pre.cores@[d]);
                assert(self.tlb@[d] == pre.tlb@[d]);
                assert(pre.acked(d) == self.acked(d));
                assert(pre.tlb@[d].contains(f));
            }
        }
    }
}

} // verus!
