//! Processes as retyped objects. A process is an order-3 block: page 0 is the root of its capability
//! table, so the table is named by the process's base; page 1 holds its record; pages 2 to 4 are kept
//! for later per-process state; pages 5 to 7 are its address space's root, record and list of cores, at
//! the offsets a device space has them. A capability names a process by its block's base and carries
//! control, and the capabilities naming it hold its block's references. See
//! design/process-holds-capabilities/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::derive::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::define::*;
use crate::layouts::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// A process's block is eight pages.
pub const PROCESS_ORDER: u8 = 3;

/// The page of a process's block that holds its record. Page 0 is its table's root.
pub const PROCESS_RECORD_PAGE: usize = 1;

/// A process capability carries control: it may destroy the process and name its table's positions.
pub const PROCESS_RIGHTS: u32 = 128;

/// What a process keeps in its record's page.
#[derive(Clone, Copy)]
pub struct ProcessRecord {
    /// Destroyed; its block waits for its references to go.
    pub dead: bool,
}

/// A process capability's payload.
pub open spec fn process_of(base: usize) -> Payload {
    Payload { kind: CapKind::Process, order: PROCESS_ORDER, rights: PROCESS_RIGHTS, base, badge: 0, reserved: 0 }
}

/// Each process's record by its block's address, the pages of its block it keeps for later, and the
/// capabilities holding its block.
pub struct Processes {
    pub records: Tracked<Map<usize, PointsTo<ProcessRecord>>>,
    /// Pages 2 to 4 of each process's block, by their own addresses.
    pub spare: Tracked<Map<usize, PagePerm4k>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
    /// The threads bound to each process, each through a binding node holding a reference to its
    /// block.
    pub bound: Ghost<IMap<usize, Set<usize>>>,
}

impl Processes {
    pub fn new() -> (ret: Self)
        ensures
            ret.records@ == Map::<usize, PointsTo<ProcessRecord>>::empty(),
            ret.spare@ == Map::<usize, PagePerm4k>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
            ret.bound@ == IMap::<usize, Set<usize>>::empty(),
    {
        Processes {
            records: Tracked(Map::tracked_empty()),
            spare: Tracked(Map::tracked_empty()),
            holders: Ghost(IMap::empty()),
            bound: Ghost(IMap::empty()),
        }
    }
}

/// The block at page b holds a process.
pub open spec fn process_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is Process
}

/// Page k of the block at p is a spare page the processes keep.
pub open spec fn spare_kept(processes: &Processes, p: usize, k: usize) -> bool {
    &&& processes.spare@.contains_key((p + k * 4096) as usize)
    &&& processes.spare@[(p + k * 4096) as usize].addr() == p + k * 4096
}

/// Two blocks of order 3 are a block apart.
pub proof fn lemma_blocks_apart(p: usize, q: usize)
    requires
        p % 32768 == 0,
        q % 32768 == 0,
        p != q,
    ensures
        p + 32768 <= q || q + 32768 <= p,
{
    lemma_fundamental_div_mod(p as int, 32768);
    lemma_fundamental_div_mod(q as int, 32768);
    let a = p as int / 32768;
    let b = q as int / 32768;
    assert(p as int == 32768 * a);
    assert(q as int == 32768 * b);
    if a < b {
        assert(32768 * a + 32768 <= 32768 * b);
    } else {
        assert(32768 * b + 32768 <= 32768 * a);
    }
}

/// The process at p has its record and its spare pages. Its block's references are exactly its
/// holders and the threads bound to it, and it is dead at once when they go.
pub open spec fn process_wf(processes: &Processes, blocks: &BlockTable, p: usize) -> bool {
    &&& p % 32768 == 0
    &&& blocks.tracks_addr_run(p, 8)
    &&& processes.records@[p].addr() == p + PROCESS_RECORD_PAGE * 4096
    &&& processes.records@[p].is_init()
    &&& spare_kept(processes, p, 2)
    &&& spare_kept(processes, p, 3)
    &&& spare_kept(processes, p, 4)
    &&& blocks.pages@[(p / 4096) as int].kind is Base
    &&& blocks.pages@[(p / 4096) as int].object is Process
    &&& blocks.pages@[(p / 4096) as int].order == 3
    &&& processes.holders@.contains_key(p)
    &&& processes.holders@[p].finite()
    &&& processes.bound@.contains_key(p)
    &&& processes.bound@[p].finite()
    &&& processes.holders@[p].len() + processes.bound@[p].len() == blocks.pages@[(p / 4096) as int].refs
    &&& blocks.pages@[(p / 4096) as int].refs == 0 ==> blocks.pages@[(p / 4096) as int].dead
}

/// Each process is well formed, a process's block is one of these, and the capabilities of kind
/// Process are exactly the holders.
pub open spec fn processes_wf(list: &Tree, tables: &Tables, processes: &Processes, blocks: &BlockTable) -> bool {
    &&& forall|p: usize| #[trigger] processes.records@.contains_key(p) ==> process_wf(processes, blocks, p)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] process_block(blocks, b)
        ==> processes.records@.contains_key((b * 4096) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Process ==> {
        &&& processes.records@.contains_key(tables.payload_of(n).base)
        &&& processes.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == PROCESS_ORDER
    }
    &&& forall|p: usize, n: usize| processes.records@.contains_key(p) && #[trigger] processes.holders@[p].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Process
        &&& tables.payload_of(n).base == p
    }
}

/// Each process has its capability table, rooted at the process's base: a table position reaches
/// the table through a capability naming the process.
pub open spec fn process_tables_wf(tables: &Tables, processes: &Processes) -> bool {
    forall|p: usize| #[trigger] processes.records@.contains_key(p) ==> tables.roots@.contains_key(p)
}

/// Each process has its address space, keyed at the process's base: a link or a map reaches the space
/// from a capability naming the process.
pub open spec fn process_spaces_wf(spaces: &Spaces, processes: &Processes) -> bool {
    forall|p: usize| #[trigger] processes.records@.contains_key(p) ==> {
        &&& spaces.roots@.contains_key(p)
        &&& spaces.records@[p].value().kind is Process
    }
}

/// Each process's holders after node i is renamed n.
pub open spec fn moved_process_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |p: usize| holders.contains_key(p),
        |p: usize| if holders[p].contains(i) { holders[p].remove(i).insert(n) } else { holders[p] },
    )
}

/// The process capabilities of a and b are the same, saying the same.
pub open spec fn same_processes(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Process ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Process ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The processes read nothing of the capabilities but the processes'.
pub proof fn lemma_processes_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    processes: &Processes,
    blocks: &BlockTable,
)
    requires
        processes_wf(list_a, tables_a, processes, blocks),
        same_processes(list_a, tables_a, list_b, tables_b),
    ensures
        processes_wf(list_b, tables_b, processes, blocks),
{
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Process implies {
        &&& processes.records@.contains_key(tables_b.payload_of(n).base)
        &&& processes.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == PROCESS_ORDER
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|p: usize, n: usize| processes.records@.contains_key(p) && #[trigger] processes.holders@[p].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Process
        &&& tables_b.payload_of(n).base == p
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_processes_same_pages(list: &Tree, tables: &Tables, processes: &Processes, a: &BlockTable, b: &BlockTable)
    requires
        processes_wf(list, tables, processes, a),
        b.pages@ == a.pages@,
    ensures
        processes_wf(list, tables, processes, b),
{
    assert forall|p: usize| #[trigger] processes.records@.contains_key(p) implies process_wf(processes, b, p) by {
        assert(process_wf(processes, a, p));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies processes.records@.contains_key((x * 4096) as usize) by {
        assert(process_block(a, x));
    }
}

/// A step that changes the count of a block that is no process's leaves every process's block as it
/// was.
pub proof fn lemma_processes_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    processes: &Processes,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        processes_wf(list_a, tables_a, processes, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is Process),
            _ => true,
        },
        same_processes(list_a, tables_a, list_b, tables_b),
    ensures
        processes_wf(list_b, tables_b, processes, b),
{
    lemma_processes_same_caps(list_a, tables_a, list_b, tables_b, processes, a);
    assert forall|p: usize| #[trigger] processes.records@.contains_key(p) implies process_wf(processes, b, p) by {
        assert(process_wf(processes, a, p));
        let x = BlockRef::Small(p / 4096);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies processes.records@.contains_key((x * 4096) as usize) by {
        assert(process_block(a, x));
    }
}

/// The processes after a free small block is typed as something that is no process: no process lay
/// in it, and a process block outside it was one before.
pub proof fn lemma_processes_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    processes: &Processes,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        processes_wf(list_a, tables_a, processes, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !((#[trigger] b.pages@[base + k]).object is Process),
        same_processes(list_a, tables_a, list_b, tables_b),
    ensures
        processes_wf(list_b, tables_b, processes, b),
{
    lemma_processes_same_caps(list_a, tables_a, list_b, tables_b, processes, a);
    assert forall|p: usize| #[trigger] processes.records@.contains_key(p) implies process_wf(processes, b, p) by {
        assert(process_wf(processes, a, p));
        let x = (p / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies processes.records@.contains_key((x * 4096) as usize) by {
        if base <= x < base + size {
            assert(!(b.pages@[base + (x - base)].object is Process));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(process_block(a, x));
    }
}

/// No process lies in a block of another kind: a process's first page is its own block's base.
pub proof fn lemma_processes_outside_block(list: &Tree, tables: &Tables, processes: &Processes, blocks: &BlockTable, base: usize)
    requires
        processes_wf(list, tables, processes, blocks),
        blocks.wf(),
        blocks.tracks(base as int),
        blocks.pages@[base as int].kind is Base,
        !(blocks.pages@[base as int].object is Process),
    ensures
        forall|p: usize| #[trigger] processes.records@.contains_key(p) ==> !blocks.in_block(base as int, (p / 4096) as int),
{
    assert forall|p: usize| #[trigger] processes.records@.contains_key(p) implies !blocks.in_block(base as int, (p / 4096) as int) by {
        assert(process_wf(processes, blocks, p));
        let x = (p / 4096) as int;
        if blocks.in_block(base as int, x) && x != base {
            blocks.lemma_member_of(base as int, x);
        }
    }
}

/// The processes after a small block that is no process's frees.
pub proof fn lemma_processes_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    processes: &Processes,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        processes_wf(list_a, tables_a, processes, a),
        a.wf(),
        a.tracks(base as int),
        a.pages@[base as int].kind is Base,
        !(a.pages@[base as int].object is Process),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_processes(list_a, tables_a, list_b, tables_b),
    ensures
        processes_wf(list_b, tables_b, processes, b),
{
    lemma_processes_outside_block(list_a, tables_a, processes, a, base);
    lemma_processes_same_caps(list_a, tables_a, list_b, tables_b, processes, a);
    assert forall|p: usize| #[trigger] processes.records@.contains_key(p) implies process_wf(processes, b, p) by {
        assert(process_wf(processes, a, p));
        assert(!a.in_block(base as int, (p / 4096) as int));
        assert(b.pages@[(p / 4096) as int] == a.pages@[(p / 4096) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies processes.records@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(process_block(a, x));
    }
}

/// The processes after the dead process at `base` goes with its block: no capability names it and no
/// thread is bound to it, and every other process lies in its own block.
pub proof fn lemma_processes_process_freed(
    list: &Tree,
    tables_a: &Tables,
    tables_b: &Tables,
    pa: &Processes,
    pb: &Processes,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        processes_wf(list, tables_a, pa, a),
        a.wf(),
        pa.records@.contains_key(base),
        a.pages@[(base / 4096) as int].refs == 0,
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block((base / 4096) as int, i) { free_entry() } else { a.pages@[i] }),
        tables_b.owner == tables_a.owner,
        tables_b.payloads == tables_a.payloads,
        pb.records@ == pa.records@.remove(base),
        pb.spare@ == pa.spare@.remove((base + 2 * 4096) as usize).remove((base + 3 * 4096) as usize).remove((base + 4 * 4096) as usize),
        pb.holders@ == pa.holders@.remove(base),
        pb.bound@ == pa.bound@.remove(base),
    ensures
        processes_wf(list, tables_b, pb, b),
        pa.holders@[base] == Set::<usize>::empty(),
        pa.bound@[base] == Set::<usize>::empty(),
        forall|p: usize| #[trigger] pb.records@.contains_key(p) ==> !a.in_block((base / 4096) as int, (p / 4096) as int),
{
    let page = (base / 4096) as int;
    assert(process_wf(pa, a, base));
    pa.holders@[base].lemma_len0_is_empty();
    pa.bound@[base].lemma_len0_is_empty();
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(base as int, 32768);
    assert forall|p: usize| #[trigger] pb.records@.contains_key(p) implies !a.in_block(page, (p / 4096) as int) by {
        assert(pa.records@.contains_key(p));
        assert(process_wf(pa, a, p));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p as int, 32768);
        let x = (p / 4096) as int;
        if a.in_block(page, x) && x != page {
            a.lemma_member_of(page, x);
        }
    }
    assert forall|p: usize| #[trigger] pb.records@.contains_key(p) implies process_wf(pb, b, p) by {
        assert(pa.records@.contains_key(p));
        assert(process_wf(pa, a, p));
        assert(p != base);
        lemma_blocks_apart(p, base);
        assert(b.pages@[(p / 4096) as int] == a.pages@[(p / 4096) as int]);
        assert(pb.spare@[(p + 2 * 4096) as usize] == pa.spare@[(p + 2 * 4096) as usize]);
        assert(pb.spare@[(p + 3 * 4096) as usize] == pa.spare@[(p + 3 * 4096) as usize]);
        assert(pb.spare@[(p + 4 * 4096) as usize] == pa.spare@[(p + 4 * 4096) as usize]);
        assert(pb.holders@[p] == pa.holders@[p]);
        assert(pb.bound@[p] == pa.bound@[p]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies pb.records@.contains_key((x * 4096) as usize) by {
        if a.in_block(page, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(process_block(a, x));
        assert(pa.records@.contains_key((x * 4096) as usize));
        assert(a.in_block(page, page));
        assert(x as int != page);
        assert((x * 4096) as usize != base);
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list, n) && tables_b.payload_of(n).kind is Process implies {
        &&& pb.records@.contains_key(tables_b.payload_of(n).base)
        &&& pb.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == PROCESS_ORDER
    } by {
        assert(tables_a.is_cap(list, n));
        assert(tables_a.payload_of(n) == tables_b.payload_of(n));
        assert(pa.holders@[tables_a.payload_of(n).base].contains(n));
        assert(tables_a.payload_of(n).base != base);
    }
    assert forall|p: usize, n: usize| pb.records@.contains_key(p) && #[trigger] pb.holders@[p].contains(n) implies {
        &&& tables_b.is_cap(list, n)
        &&& tables_b.payload_of(n).kind is Process
        &&& tables_b.payload_of(n).base == p
    } by {
        assert(pa.holders@[p].contains(n));
        assert(tables_a.is_cap(list, n));
        assert(tables_a.payload_of(n) == tables_b.payload_of(n));
    }
}

/// The processes after thread t's binding to p comes, with one more reference on p's block.
pub proof fn lemma_processes_bound_added(
    list: &Tree,
    tables: &Tables,
    a: &Processes,
    b: &Processes,
    ba: &BlockTable,
    bb: &BlockTable,
    p: usize,
    t: usize,
)
    requires
        processes_wf(list, tables, a, ba),
        a.records@.contains_key(p),
        !a.bound@[p].contains(t),
        b.records == a.records,
        b.spare == a.spare,
        b.holders == a.holders,
        b.bound@ == a.bound@.insert(p, a.bound@[p].insert(t)),
        block_refs(ba, BlockRef::Small(p / 4096)) < usize::MAX,
        blocks_refs_changed(
            ba,
            bb,
            BlockRef::Small(p / 4096),
            (block_refs(ba, BlockRef::Small(p / 4096)) + 1) as usize,
            block_dead(ba, BlockRef::Small(p / 4096)),
        ),
    ensures
        processes_wf(list, tables, b, bb),
{
    let br = BlockRef::Small(p / 4096);
    assert(process_wf(a, ba, p));
    vstd::set::lemma_set_insert_len(a.bound@[p], t);
    assert forall|u: usize| #[trigger] b.records@.contains_key(u) implies process_wf(b, bb, u) by {
        assert(process_wf(a, ba, u));
        if u != p {
            lemma_table_pages_distinct(u, p);
            let x = BlockRef::Small(u / 4096);
            assert(block_typed(ba, x));
            assert(x != br);
            assert(block_refs(bb, x) == block_refs(ba, x));
            assert(block_dead(bb, x) == block_dead(ba, x));
            assert(b.bound@[u] == a.bound@[u]);
        }
    }
    assert forall|x: usize| bb.tracks(x as int) && #[trigger] process_block(bb, x) implies b.records@.contains_key((x * 4096) as usize) by {
        assert(process_block(ba, x));
    }
    assert forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Process implies {
        &&& b.records@.contains_key(tables.payload_of(n).base)
        &&& b.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == PROCESS_ORDER
    } by {}
    assert forall|u: usize, n: usize| b.records@.contains_key(u) && #[trigger] b.holders@[u].contains(n) implies {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Process
        &&& tables.payload_of(n).base == u
    } by {
        assert(a.holders@[u].contains(n));
    }
}

/// The processes after thread t's binding to p goes, taking its reference on p's block with it.
pub proof fn lemma_processes_bound_dropped(
    list: &Tree,
    tables: &Tables,
    a: &Processes,
    b: &Processes,
    ba: &BlockTable,
    bb: &BlockTable,
    p: usize,
    t: usize,
)
    requires
        processes_wf(list, tables, a, ba),
        a.records@.contains_key(p),
        a.bound@[p].contains(t),
        b.records == a.records,
        b.spare == a.spare,
        b.holders == a.holders,
        b.bound@ == a.bound@.insert(p, a.bound@[p].remove(t)),
        blocks_refs_changed(
            ba,
            bb,
            BlockRef::Small(p / 4096),
            (block_refs(ba, BlockRef::Small(p / 4096)) - 1) as usize,
            block_dead(ba, BlockRef::Small(p / 4096)) || block_refs(ba, BlockRef::Small(p / 4096)) == 1,
        ),
    ensures
        processes_wf(list, tables, b, bb),
{
    let br = BlockRef::Small(p / 4096);
    assert(process_wf(a, ba, p));
    vstd::set::lemma_set_remove_len(a.bound@[p], t);
    assert forall|u: usize| #[trigger] b.records@.contains_key(u) implies process_wf(b, bb, u) by {
        assert(process_wf(a, ba, u));
        if u != p {
            lemma_table_pages_distinct(u, p);
            let x = BlockRef::Small(u / 4096);
            assert(block_typed(ba, x));
            assert(x != br);
            assert(block_refs(bb, x) == block_refs(ba, x));
            assert(block_dead(bb, x) == block_dead(ba, x));
            assert(b.bound@[u] == a.bound@[u]);
        }
    }
    assert forall|x: usize| bb.tracks(x as int) && #[trigger] process_block(bb, x) implies b.records@.contains_key((x * 4096) as usize) by {
        assert(process_block(ba, x));
    }
    assert forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Process implies {
        &&& b.records@.contains_key(tables.payload_of(n).base)
        &&& b.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == PROCESS_ORDER
    } by {}
    assert forall|u: usize, n: usize| b.records@.contains_key(u) && #[trigger] b.holders@[u].contains(n) implies {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Process
        &&& tables.payload_of(n).base == u
    } by {
        assert(a.holders@[u].contains(n));
    }
}

impl CapKernel {
    /// A process capability names a process, whose block holds its reference, lies in no typed region
    /// and so is read as the small block at its base.
    pub proof fn lemma_process_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Process,
        ensures
            self.processes.records@.contains_key(self.payload_of(n).base),
            self.processes.holders@[self.payload_of(n).base].contains(n),
            self.payload_of(n).base % 32768 == 0,
            self.blocks.tracks_addr(self.payload_of(n).base),
            self.payload_of(n).order == PROCESS_ORDER,
            self.blocks.pages@[(self.payload_of(n).base / 4096) as int].object is Process,
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / 4096) == BlockRef::Small(self.payload_of(n).base / 4096),
    {
        let p = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(process_wf(&self.processes, &self.blocks, p));
        if self.processes.holders@[p].len() == 0 {
            self.processes.holders@[p].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((p / 4096) as int);
    }

    /// A process capability names the process's space, keyed at its base.
    pub proof fn lemma_process_space(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Process,
        ensures
            self.spaces.roots@.contains_key(self.payload_of(n).base),
            self.spaces.records@[self.payload_of(n).base].value().kind is Process,
    {
        self.lemma_process_cap(n);
    }

    /// The processes after process capability n, the only capability that changed, joins process p
    /// with one more reference on its block.
    pub proof fn lemma_processes_holder_added(pre: Self, post: Self, n: usize, p: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            !pre.is_cap(n),
            post.is_cap(n),
            post.payload_of(n).kind is Process,
            post.payload_of(n).base == p,
            post.payload_of(n).order == PROCESS_ORDER,
            pre.processes.records@.contains_key(p),
            block_refs(&pre.blocks, BlockRef::Small(p / 4096)) < usize::MAX,
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(p / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(p / 4096)) + 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(p / 4096)),
            ),
            post.processes.records == pre.processes.records,
            post.processes.spare == pre.processes.spare,
            post.processes.bound == pre.processes.bound,
            post.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].insert(n)),
        ensures
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        let ha = pre.processes.holders@;
        let hb = post.processes.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(p / 4096);
        assert(process_wf(&pre.processes, a, p));
        assert(!ha[p].contains(n));
        vstd::set::lemma_set_insert_len(ha[p], n);
        assert forall|u: usize| #[trigger] post.processes.records@.contains_key(u)
            implies process_wf(&post.processes, b, u) by {
            assert(process_wf(&pre.processes, a, u));
            if u != p {
                lemma_table_pages_distinct(u, p);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x)
            implies post.processes.records@.contains_key((x * 4096) as usize) by {
            assert(process_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
            &&& post.processes.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == PROCESS_ORDER
        } by {
            if x != n {
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
        assert forall|u: usize, x: usize| post.processes.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Process
            &&& post.tables.payload_of(x).base == u
        } by {
            if !(u == p && x == n) {
                assert(ha[u].contains(x));
                assert(pre.tables.is_cap(&pre.list, x));
                assert(x != n);
            }
        }
    }

    /// The processes after process capability n, the only capability that changed, leaves process p,
    /// taking its reference on the block with it.
    pub proof fn lemma_processes_holder_dropped(pre: Self, post: Self, n: usize, p: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            pre.payload_of(n).kind is Process,
            pre.payload_of(n).base == p,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(p / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(p / 4096)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(p / 4096)) || block_refs(&pre.blocks, BlockRef::Small(p / 4096)) == 1,
            ),
            post.processes.records == pre.processes.records,
            post.processes.spare == pre.processes.spare,
            post.processes.bound == pre.processes.bound,
            post.processes.holders@ == pre.processes.holders@.insert(p, pre.processes.holders@[p].remove(n)),
        ensures
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        let ha = pre.processes.holders@;
        let hb = post.processes.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(p / 4096);
        pre.lemma_process_cap(n);
        assert(process_wf(&pre.processes, a, p));
        assert(ha[p].contains(n));
        vstd::set::lemma_set_remove_len(ha[p], n);
        assert forall|u: usize| #[trigger] post.processes.records@.contains_key(u)
            implies process_wf(&post.processes, b, u) by {
            assert(process_wf(&pre.processes, a, u));
            if u != p {
                lemma_table_pages_distinct(u, p);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x)
            implies post.processes.records@.contains_key((x * 4096) as usize) by {
            assert(process_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
            &&& post.processes.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == PROCESS_ORDER
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|u: usize, x: usize| post.processes.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Process
            &&& post.tables.payload_of(x).base == u
        } by {
            assert(ha[u].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// What a process's retype does to the block table: the free order-3 block at `page` is typed as
    /// the process at `base`, the list gains no page, and no holder changed.
    proof fn lemma_process_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.blocks.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page % 8 == 0,
            pre.blocks.tracks_run(page as int, 8),
            !pre.blocks.covered(page as int),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Process,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            post.list.pages@.dom() == pre.list.pages@.dom(),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child).kind is Process,
        ensures
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            zeroing_typed(&post.zeroing, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        assert forall|k: int| 0 < k < 8 implies {
            &&& (#[trigger] b.pages@[page + k]).kind is Member
            &&& b.pages@[page + k].base == page
        } by {
            b.lemma_member_of(page as int, page + k);
        }
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!pre.is_cap(child));
        assert(a.member_bases_wf());
        lemma_list_pages_used_small_typed(&pre.list, a, b, page, 8);
        lemma_list_pages_used_subset(&pre.list, &post.list, b);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 3);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 8);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 8);
        assert forall|l: usize| #[trigger] pre.tables.owner@.contains_key(l) implies {
            &&& post.list.nodes@[l as int].live == pre.list.nodes@[l as int].live
            &&& post.list.nodes@[l as int].kind == pre.list.nodes@[l as int].kind
        } by {
            pre.tables.lemma_leaf(&pre.list, l);
            lemma_leaf_page(l);
            assert(page_of(l) == l);
            assert(pre.list.valid(l));
            assert(l != child);
        }
        assert(leaf_blocks_wf(&pre.list, &post.tables, b));
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &post.tables, b);
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, a, b, page, 8);
        assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x)
            implies pre.table_pages.maps@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert(b.pages@[page as int].object is Process);
            } else if page < x < page + 8 {
                assert(b.pages@[page + (x - page)].kind is Member);
            }
        }
        assert(table_pages_wf(&pre.list, &pre.table_pages, b));
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != child);
        }
        lemma_table_pages_same_nodes(&pre.list, &post.list, &pre.table_pages, b);
    }

    /// The spaces after a process's retype: the new one lies in the process's block with what the
    /// block gave, held by no space capability, and every other lay outside the block and keeps its
    /// pages and holders.
    proof fn lemma_spaces_process_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            pre.blocks.tracks_run(page as int, 8),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Process,
            post.blocks.pages@[page as int].order == 3,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.roots@[base].addr() == base + SPACE_ROOT_PAGE * 4096,
            post.spaces.roots@[base].is_init(),
            post.spaces.roots@[base].value().wf(),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            post.spaces.records@[base].addr() == base + SPACE_RECORD_PAGE * 4096,
            post.spaces.records@[base].is_init(),
            post.spaces.records@[base].value().root == base + SPACE_ROOT_PAGE * 4096,
            post.spaces.records@[base].value().kind is Process,
            post.spaces.loaded@ == pre.spaces.loaded@.insert(base, post.spaces.loaded@[base]),
            post.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * 4096,
            post.spaces.loaded@[base].is_init(),
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            kernel_slots_wf(&post.spaces, base),
            root_record_wf(&post.spaces, base),
            post.spaces.holders@ == pre.spaces.holders@.insert(base, Set::<usize>::empty()),
            post.spaces.bound@ == pre.spaces.bound@.insert(base, Set::<usize>::empty()),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == process_of(base),
        ensures
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let sa = &pre.spaces;
        let sb = &post.spaces;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!sa.roots@.contains_key(base)) by {
            if sa.roots@.contains_key(base) {
                assert(space_wf(&pre.list, sa, a, base));
                assert(a.pages@[page + 0int].kind is Free);
            }
        }
        assert(!pre.is_cap(child));
        assert forall|s: usize| #[trigger] sb.roots@.contains_key(s) implies space_wf(&post.list, sb, b, s) by {
            if s == base {
                assert(sb.holders@[base] == Set::<usize>::empty());
                assert(sb.bound@[base] == Set::<usize>::empty());
            } else {
                assert(sa.roots@.contains_key(s));
                assert(space_wf(&pre.list, sa, a, s));
                let x = (s / 4096) as int;
                if page <= x < page + 8 {
                    assert(a.pages@[page + (x - page)].kind is Free);
                }
                assert(b.pages@[x] == a.pages@[x]);
                assert(sb.roots@[s] == sa.roots@[s]);
                assert(sb.records@[s] == sa.records@[s]);
                assert(sb.loaded@[s] == sa.loaded@[s]);
                assert(sb.holders@[s] == sa.holders@[s]);
                assert(sb.bound@[s] == sa.bound@[s]);
                if sa.records@[s].value().kind is Device {
                    assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
                        assert(pre.list.pages@.dom().contains(table_node_page(s, k)));
                    }
                }
                assert(root_record_wf(sb, s)) by {
                    assert(root_record_wf(sa, s));
                }
                assert(kernel_slots_wf(sb, s)) by {
                    assert(kernel_slots_wf(sa, s));
                }
            }
        }
        assert forall|s: usize| #[trigger] sb.loaded@.contains_key(s) implies sb.roots@.contains_key(s) by {
            if s != base {
                assert(sa.loaded@.contains_key(s));
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies sb.roots@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert(b.pages@[page as int].object is Process);
            } else if page < x < page + 8 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(space_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Space implies {
            &&& sb.roots@.contains_key(post.tables.payload_of(n).base)
            &&& sb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == 3
        } by {
            assert(n != child);
            assert(pre.tables.is_cap(&pre.list, n));
            let t = pre.tables.payload_of(n).base;
            assert(sa.roots@.contains_key(t));
            assert(sa.holders@[t].contains(n));
            assert(t != base);
            assert(sb.holders@[t] == sa.holders@[t]);
        }
        assert forall|s: usize, n: usize| sb.roots@.contains_key(s) && #[trigger] sb.holders@[s].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Space
            &&& post.tables.payload_of(n).base == s
        } by {
            assert(s != base);
            assert(sa.roots@.contains_key(s));
            assert(sa.holders@[s].contains(n));
            assert(pre.tables.is_cap(&pre.list, n));
            assert(n != child);
        }
    }

    /// The processes after a process's retype at base: the new one has its record and spare pages and
    /// holds its one capability, and every other lay outside the block and keeps its holders.
    proof fn lemma_processes_process_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            pre.blocks.tracks_run(page as int, 8),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Process,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            post.processes.records@ == pre.processes.records@.insert(base, post.processes.records@[base]),
            post.processes.records@[base].addr() == base + PROCESS_RECORD_PAGE * 4096,
            post.processes.records@[base].is_init(),
            forall|q: usize| #[trigger] pre.processes.spare@.contains_key(q) && q != (base + 2 * 4096) as usize
                && q != (base + 3 * 4096) as usize && q != (base + 4 * 4096) as usize ==> {
                &&& post.processes.spare@.contains_key(q)
                &&& post.processes.spare@[q] == pre.processes.spare@[q]
            },
            spare_kept(&post.processes, base, 2),
            spare_kept(&post.processes, base, 3),
            spare_kept(&post.processes, base, 4),
            post.processes.holders@ == pre.processes.holders@.insert(base, set![child]),
            post.processes.bound@ == pre.processes.bound@.insert(base, Set::<usize>::empty()),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == process_of(base),
        ensures
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let pa = &pre.processes;
        let pb = &post.processes;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!pa.records@.contains_key(base)) by {
            if pa.records@.contains_key(base) {
                assert(process_wf(pa, a, base));
                assert(a.pages@[page + 0int].kind is Free);
            }
        }
        assert(!pre.is_cap(child));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|p: usize| #[trigger] pb.records@.contains_key(p) implies process_wf(pb, b, p) by {
            if p == base {
                assert(pb.holders@[base] == set![child]);
                assert(pb.holders@[base].finite());
                assert(pb.bound@[base] == Set::<usize>::empty());
                assert(pb.bound@[base].len() == 0);
            } else {
                assert(pa.records@.contains_key(p));
                assert(process_wf(pa, a, p));
                let x = (p / 4096) as int;
                if page <= x < page + 8 {
                    assert(a.pages@[page + (x - page)].kind is Free);
                }
                assert(b.pages@[x] == a.pages@[x]);
                assert(pb.records@[p] == pa.records@[p]);
                assert(pb.holders@[p] == pa.holders@[p]);
                assert(pb.bound@[p] == pa.bound@[p]);
                lemma_blocks_apart(p, base);
                assert(spare_kept(pa, p, 2));
                assert(spare_kept(pa, p, 3));
                assert(spare_kept(pa, p, 4));
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] process_block(b, x) implies pb.records@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
            } else if page < x < page + 8 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(process_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Process implies {
            &&& pb.records@.contains_key(post.tables.payload_of(n).base)
            &&& pb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == PROCESS_ORDER
        } by {
            if n == child {
                assert(pb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let p = pre.tables.payload_of(n).base;
                assert(pa.records@.contains_key(p));
                assert(p != base);
                assert(pb.holders@[p] == pa.holders@[p]);
            }
        }
        assert forall|p: usize, n: usize| pb.records@.contains_key(p) && #[trigger] pb.holders@[p].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Process
            &&& post.tables.payload_of(n).base == p
        } by {
            if p == base {
                assert(n == child);
            } else {
                assert(pa.records@.contains_key(p));
                assert(pa.holders@[p].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The view of a process's retype: one child under the untyped, naming the new process, whose table
    /// root was no root before and holds no leaf, so it holds nothing.
    proof fn lemma_process_view(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize)
        requires
            Self::adds_cap(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(&pre.list, root, from),
            pre.tables.has_slot(&pre.list, root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            post.payload_of(pre.tables.node_of(root, to)) == process_of(base),
            block_within(base, PROCESS_ORDER, pre.payload_of(pre.tables.node_of(root, from))),
            !pre.tables.roots@.contains_key(base),
        ensures
            post.view().holds(root, pre.tables.node_of(root, to)),
            adds_object(
                pre.view(),
                post.view(),
                root,
                pre.tables.node_of(root, from),
                pre.tables.node_of(root, to),
                |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live,
                base,
            ),
    {
        let parent = pre.tables.node_of(root, from);
        let child = pre.tables.node_of(root, to);
        let (a, b) = (pre.view(), post.view());
        Self::lemma_places_node_view(pre, post, root, from, root, to);
        let pp = pre.payload_of(parent);
        lemma2_to64();
        assert(block_bytes(PROCESS_ORDER) == 32768);
        assert(block_bytes(pp.order) == a.pages[parent] * 4096);
        assert(a.covers(parent, base)) by {
            assert(a.names.contains_key(parent));
            assert(a.pages.contains_key(parent));
            assert(a.names[parent] == pp.base);
            assert(block_within(base, PROCESS_ORDER, pp));
            assert(base as int % 32768 == 0);
            vstd::arithmetic::div_mod::lemma_mod_mod(base as int, 4096, 8);
            assert(base % 4096 == 0);
            assert(base + 32768 <= pp.base + a.pages[parent] * 4096);
            assert(a.names[parent] <= base < a.names[parent] + a.pages[parent] * 4096);
        }
        assert forall|x: NodeId| !#[trigger] b.held.contains((base, x)) by {
            if b.held.contains((base, x)) {
                assert(post.tables.owner@.contains_key(page_of(x)));
                pre.tables.lemma_leaf(&pre.list, page_of(x));
                assert(pre.tables.owner@[page_of(x)].0 == base);
            }
        }
        assert(b.names[child] == base);
    }

    /// What a process's retype leaves as it was: its derive changed the liveness of the new capability
    /// alone and no node's depth, its table root is a new one, and the block table's pages outside
    /// the new block are as they were.
    proof fn lemma_process_keeps(pre: Self, post: Self, mid: Tree, root: usize, to: usize, page: int)
        requires
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, to),
            !pre.list.nodes@[pre.tables.node_of(root, to) as int].live,
            mid == pre.list,
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
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies {
            &&& post.is_cap(x)
            &&& post.payload_of(x) == pre.payload_of(x)
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        } by {
            pre.lemma_slot_bound(x);
            assert(x != child);
            assert(post.list.nodes@[x as int].depth == mid.nodes@[x as int].depth);
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

    /// Retypes the free order-3 block at `base` as a process, under the untyped at index `from` of the
    /// table at `root`, with its capability at the empty index `to`: an empty capability table whose
    /// root is the block's first page, a record that says it is live, and an address space holding the
    /// kernel's entries and nothing else, loaded on no core. All of these come from user space, and a
    /// refusal changes nothing.
    pub fn retype_process(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).cores == old(self).cores,
            final(self).iommus == old(self).iommus,
            ret == old(self).can_retype_block(root, from, to, base, PROCESS_ORDER),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                let page = (base / 4096) as int;
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& final(self).blocks.pages@[page].kind is Base
                &&& final(self).blocks.pages@[page].object is Process
                &&& final(self).blocks.pages@[page].order == 3
                &&& final(self).blocks.pages@[page].refs == 1
                &&& !final(self).blocks.pages@[page].dead
                &&& forall|i: int| old(self).blocks.tracks(i) && !(page <= i < page + 8)
                    ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i]
                &&& final(self).table_pages == old(self).table_pages
                &&& final(self).spaces.roots@ == old(self).spaces.roots@.insert(base, final(self).spaces.roots@[base])
                &&& final(self).spaces.records@ == old(self).spaces.records@.insert(base, final(self).spaces.records@[base])
                &&& final(self).tables.roots@.contains_key(base)
                &&& forall|r: int| 0 <= r < ROOT_ENTRIES ==> #[trigger] final(self).tables.leaf(base, r) == NO_LEAF
                &&& final(self).spaces.roots@.contains_key(base)
                &&& final(self).spaces.records@[base].value().kind is Process
                &&& final(self).spaces.records@[base].value().table == fresh_root(base)
                &&& forall|i: usize| i < 512 && !holds_kernel(SpaceKind::Process, i)
                    ==> #[trigger] final(self).spaces.roots@[base].value()[i].is_empty()
                &&& kernel_slots_wf(&final(self).spaces, base)
                &&& final(self).spaces.kernel_entries == old(self).spaces.kernel_entries
                &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] final(self).loaded(c, base)
                &&& final(self).process_unloaded(base)
                &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, c, base)
                &&& space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty()
                &&& forall|r: usize| #[trigger] old(self).spaces.roots@.contains_key(r) ==>
                    space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                        == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r)
                &&& final(self).processes.records@.contains_key(base)
                &&& !final(self).processes.records@[base].value().dead
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == process_of(base)
                &&& final(self).payload_of(child).rights & right_bit(Right::Control) != 0
                &&& final(self).list.is_child(parent, child)
                &&& final(self).list.parent@ == old(self).list.parent@.insert(child, parent)
                &&& final(self).list.nodes@[child as int].depth == old(self).list.nodes@[parent as int].depth + 1
                &&& Self::retype_keeps(*old(self), *final(self), child, page, 3, None)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, PROCESS_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        if !self.blocks.run_tracked(base / 4096, 8) {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(block_bytes(3) == 32768);
            assert(base % 32768 == 0);
            lemma_table_page_base(base, page);
        }
        let Tracked(perms) = match self.blocks.try_type(page, 3, ObjectType::Process) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let ghost all = perms;
        let tracked mut table_root;
        let tracked record;
        let tracked spare2;
        let tracked spare3;
        let tracked spare4;
        let tracked space_root;
        let tracked space_record;
        let tracked space_cores;
        proof {
            assert forall|k: usize| k < 8 implies #[trigger] holds(all, (page + k) as usize) by {
                assert(all[(page + k) as usize].addr() == (page + k) * 4096);
            }
            assert(holds(all, (page + 0) as usize));
            assert(holds(all, (page + 1) as usize));
            assert(holds(all, (page + 2) as usize));
            assert(holds(all, (page + 3) as usize));
            assert(holds(all, (page + 4) as usize));
            assert(holds(all, (page + 5) as usize));
            assert(holds(all, (page + 6) as usize));
            assert(holds(all, (page + 7) as usize));
            table_root = perms.tracked_remove(page);
            record = perms.tracked_remove((page + 1) as usize);
            spare2 = perms.tracked_remove((page + 2) as usize);
            spare3 = perms.tracked_remove((page + 3) as usize);
            spare4 = perms.tracked_remove((page + 4) as usize);
            space_root = perms.tracked_remove((page + 5) as usize);
            space_record = perms.tracked_remove((page + 6) as usize);
            space_cores = perms.tracked_remove((page + 7) as usize);
            // The first page's permission is ours, so no table root lies there.
            if pre.tables.roots@.contains_key(base) {
                lemma_thread_block_layouts();
                table_root.is_distinct(self.tables.roots.borrow().tracked_borrow(base));
                pre.tables.lemma_root(base);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
            pre.list.lemma_seq_fits();
        }
        self.tables.put_root(&self.list, base, Tracked(table_root));
        let ghost rooted = self.tables;
        let tracked mut typed_record = page_into_process_record(record);
        PPtr::<ProcessRecord>::from_usize(base + PROCESS_RECORD_PAGE * 4096).put(Tracked(&mut typed_record), ProcessRecord { dead: false });
        proof {
            self.processes.records.borrow_mut().tracked_insert(base, typed_record);
            self.processes.spare.borrow_mut().tracked_insert((base + 2 * 4096) as usize, spare2);
            self.processes.spare.borrow_mut().tracked_insert((base + 3 * 4096) as usize, spare3);
            self.processes.spare.borrow_mut().tracked_insert((base + 4 * 4096) as usize, spare4);
        }
        let root_table = base + SPACE_ROOT_PAGE * 4096;
        let (_, Tracked(map)) = page_perm_to_page_map(root_table, Ghost(4), Tracked(space_root));
        let tracked mut map = map;
        page_map_set_kernel_entry_range(&self.spaces.kernel_entries, root_table, Tracked(&mut map));
        let tracked mut typed;
        let tracked mut cores;
        proof {
            typed = page_into_space_record(space_record);
            cores = page_into_core_list(space_cores);
        }
        let ids = vstd::array::array_fill_for_copy_types::<usize, NUM_CPUS>(0usize);
        PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).put(Tracked(&mut cores), SpaceCores { list: 0u32, ids });
        PPtr::<SpaceRecord>::from_usize(base + SPACE_RECORD_PAGE * 4096).put(
            Tracked(&mut typed),
            SpaceRecord {
                kind: SpaceKind::Process,
                root: root_table,
                table: TableRecord { level: 4, space: Some(base), parent: None, written: false },
            },
        );
        proof {
            self.spaces.roots.borrow_mut().tracked_insert(base, map);
            self.spaces.records.borrow_mut().tracked_insert(base, typed);
            self.spaces.loaded.borrow_mut().tracked_insert(base, cores);
        }
        let ghost mid = self.list;
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            self.tables.lemma_wf_same_pages(&mid, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Process, order: PROCESS_ORDER, rights: PROCESS_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.processes.holders = Ghost(pre.processes.holders@.insert(base, set![child]));
        self.processes.bound = Ghost(pre.processes.bound@.insert(base, Set::<usize>::empty()));
        self.spaces.holders = Ghost(pre.spaces.holders@.insert(base, Set::<usize>::empty()));
        self.spaces.bound = Ghost(pre.spaces.bound@.insert(base, Set::<usize>::empty()));
        proof {
            let post = *self;
            assert(mid == pre.list);
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                pre.list.lemma_valid_bound(x);
            }
            assert(Self::space_step(pre, post, child));
            assert(post.payload_of(child) == process_of(base));
            assert(payload_wf(post.payload_of(child)));
            assert(post.is_cap(child));
            Self::lemma_space_caps_wf(pre, post, child);
            assert forall|s: usize| #[trigger] pre.spaces.loaded@.contains_key(s) implies {
                &&& post.spaces.loaded@.contains_key(s)
                &&& post.spaces.loaded@[s].value() == pre.spaces.loaded@[s].value()
            } by {
                assert(pre.spaces.roots@.contains_key(s));
                assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, s));
                assert(s != base);
            }
            Self::lemma_tlb_same(pre, post);
            assert(list_grown(pre.list, mid));
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            assert(!pre.spaces.roots@.contains_key(base)) by {
                if pre.spaces.roots@.contains_key(base) {
                    assert(space_wf(&pre.list, &pre.spaces, &pre.blocks, base));
                    assert(pre.blocks.pages@[page as int].kind is Free);
                }
            }
            assert(post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]));
            assert(post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]));
            assert(post.spaces.loaded@ == pre.spaces.loaded@.insert(base, post.spaces.loaded@[base]));
            Self::lemma_space_nodes_frame(pre, post, child, child);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            assert forall|k: int| 0 < k < 8 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
                post.blocks.lemma_member_of(page as int, page + k);
            }
            Self::lemma_process_blocks(pre, post, base, page, child);
            assert forall|c: int| 0 <= c < NUM_CPUS implies #[trigger] post.spaces.loaded@[base].value().ids@[c] == 0usize by {
                broadcast use vstd::array::axiom_spec_array_fill_for_copy_type;
                assert(vstd::array::spec_array_fill_for_copy_type::<usize, NUM_CPUS>(0usize).view()[c] == 0usize);
            }
            lemma_ids_space_added(pre.cores@, pre.spaces.loaded@, post.spaces.loaded@, base);
            assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] holds_id(post.cores@, post.spaces.loaded@, c, base) by {
                pre.lemma_id_handed_out(c, base, 0);
                assert(post.spaces.loaded@[base].value().ids@[c] == 0usize);
                assert(id_generation(0usize) == 0);
            }
            assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] post.loaded(c, base) by {
                assert(post.spaces.loaded@[base].value().list == 0u32);
                lemma_no_core_listed(c as u32);
            }
            Self::lemma_spaces_process_added(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 8 implies !((#[trigger] post.blocks.pages@[page + k]).object is Thread) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Process);
                }
            }
            lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page, 8);
            assert(!pre.processes.records@.contains_key(base)) by {
                if pre.processes.records@.contains_key(base) {
                    assert(process_wf(&pre.processes, &pre.blocks, base));
                    assert(pre.blocks.pages@[page as int].kind is Free);
                }
            }
            assert(spare_kept(&post.processes, base, 2));
            assert(spare_kept(&post.processes, base, 3));
            assert(spare_kept(&post.processes, base, 4));
            assert(post.processes.records@ == pre.processes.records@.insert(base, post.processes.records@[base]));
            Self::lemma_processes_process_added(pre, post, base, page, child);
            Self::lemma_space_links(pre, post, base, page);
            Self::lemma_space_mappings(pre, post, base, page);
            assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
                pre.lemma_mapping_node(n);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_mappings_grown(pre, post, page, 3);
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
                assert(x != child);
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_devices_same_caps(pre, post);
            assert(post.tables.roots == rooted.roots);
            assert forall|p: usize| #[trigger] post.processes.records@.contains_key(p) implies post.tables.roots@.contains_key(p) by {
                if p != base {
                    assert(pre.processes.records@.contains_key(p));
                }
            }
            lemma_binding_nodes_grown(pre.list, mid, post.list, child, child);
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_binding_parents_same_caps(pre, post);
            assert(post.wf());
            Self::lemma_bound_threads_same(pre, post);
            assert(PROCESS_RIGHTS & 128 != 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_process_view(pre, post, root, from, to, base);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_object_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
            assert(post.tables.roots == rooted.roots);
            assert forall|r: int| 0 <= r < ROOT_ENTRIES implies #[trigger] post.tables.leaf(base, r) == NO_LEAF by {
                assert(rooted.leaf(base, r) == NO_LEAF);
            }
            Self::lemma_process_keeps(pre, post, mid, root, to, page as int);
        }
        true
    }
}


} // verus!
