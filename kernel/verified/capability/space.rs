//! Address spaces as retyped objects. A table page is an order-3 block: 5 node pages, whose node 0 is
//! the block's hidden node, then the table, then its record, then a spare page. So an entry finds its mapping's node
//! in constant time, and whoever maps pays for the table. See design/address-spaces-as-objects/.
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::array::*;
use crate::capability::device::*;
use crate::capability::mapping::*;
use crate::capability::block::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::list::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::retype::*;
use crate::capability::table::*;
use crate::capability::process::*;
use crate::capability::thread::*;
use crate::capability::view::*;
use crate::layouts::*;
use crate::define::*;
use crate::arch::usize2page_entry;
use crate::pagetable::entry::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::pagemap_util_t::*;
use crate::pptr::*;

/// The page of a table page's block that holds its record.
pub const TABLE_RECORD_PAGE: usize = 6;

/// The node pages of a table page's block, first in it, so its hidden node is at its address.
pub const TABLE_NODE_PAGES: usize = 5;

/// The permissions of each table page's table, record and spare page, by the block's address, the spare
/// page's by its own.
pub struct TablePages {
    pub maps: Tracked<Map<usize, PointsTo<PageMap>>>,
    pub records: Tracked<Map<usize, PointsTo<TableRecord>>>,
    pub spare: Tracked<Map<usize, PagePerm4k>>,
}

/// A space's kind, named for what walks its table: a process's threads on a core, or a device through its
/// IOMMU.
#[derive(Clone, Copy)]
pub enum SpaceKind {
    Process,
    Device,
}

/// The table and entry that point at a table.
#[derive(Clone, Copy)]
pub struct TableParent {
    pub table: usize,
    pub entry: usize,
}

/// What a table keeps about itself. Its level is fixed when it is typed. Its space and parent are absent
/// until it is linked. Written says whether any entry has ever been written, so that an empty table is
/// known in constant time.
#[derive(Clone, Copy)]
pub struct TableRecord {
    pub level: usize,
    pub space: Option<usize>,
    pub parent: Option<TableParent>,
    pub written: bool,
}

/// A table page's record when it is typed.
pub open spec fn fresh_table(level: usize) -> TableRecord {
    TableRecord { level, space: None, parent: None, written: false }
}

/// A space root's record when it is typed. A root is level 4, belongs to its space and has no parent.
pub open spec fn fresh_root(s: usize) -> TableRecord {
    TableRecord { level: 4, space: Some(s), parent: None, written: false }
}

/// What a space's block keeps beside its tables. The root is reached through this pointer, never from
/// the block's layout.
#[derive(Clone, Copy)]
pub struct SpaceRecord {
    pub kind: SpaceKind,
    pub root: usize,
    pub table: TableRecord,
}

/// A space's page of a block: its root table, its record and the list of cores that have loaded it.
pub const SPACE_ROOT_PAGE: usize = 5;
pub const SPACE_RECORD_PAGE: usize = 6;
pub const SPACE_CORES_PAGE: usize = 7;

/// What a space keeps per core: the list of cores that have loaded it, and its id on each.
#[derive(Clone, Copy)]
pub struct SpaceCores {
    pub list: u32,
    /// The space's word on each core, its PCID's generation in the high bits and the PCID in the low 12.
    /// A new space's words are zero, and generation zero is never current, so it holds no id.
    pub ids: [usize; NUM_CPUS],
}

/// Core c is on this list of cores, one bit per core.
pub open spec fn core_listed(cores: u32, c: int) -> bool {
    (cores >> (c as u32)) & 1u32 == 1u32
}

/// Adding core c to a list puts c on it and leaves the others.
pub proof fn lemma_core_added(cores: u32, c: u32, d: u32)
    requires
        c < 32,
        d < 32,
    ensures
        ((cores | (1u32 << c)) >> d) & 1u32 == 1u32 <==> d == c || (cores >> d) & 1u32 == 1u32,
{
    assert(((cores | (1u32 << c)) >> d) & 1u32 == 1u32 <==> d == c || (cores >> d) & 1u32 == 1u32) by (bit_vector)
        requires
            c < 32,
            d < 32,
    ;
}

/// The empty list has no core on it.
pub proof fn lemma_no_core_listed(d: u32)
    requires
        d < 32,
    ensures
        (0u32 >> d) & 1u32 != 1u32,
{
    assert((0u32 >> d) & 1u32 != 1u32) by (bit_vector)
        requires
            d < 32,
    ;
}

/// A space capability carries write: it may change what the space maps.
pub const SPACE_RIGHTS: u32 = 2;

/// A space capability's payload.
pub open spec fn space_of(base: usize) -> Payload {
    Payload { kind: CapKind::Space, order: 3, rights: SPACE_RIGHTS, base, badge: 0, reserved: 0 }
}

/// Each space's permissions by its block's address, and the capabilities holding its block.
pub struct Spaces {
    pub roots: Tracked<Map<usize, PointsTo<PageMap>>>,
    pub records: Tracked<Map<usize, PointsTo<SpaceRecord>>>,
    /// The cores that have loaded each space. A bit stays set after a flush, since a flush cannot
    /// visit every space in bounded time, and a core past a flush may hold nothing, which costs at
    /// most a spare IPI.
    pub loaded: Tracked<Map<usize, PointsTo<SpaceCores>>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
    /// The devices bound to each device space, each holding a reference to its block. atmo-6x9.16.14 binds
    /// the first.
    pub bound: Ghost<IMap<usize, Set<usize>>>,
    /// The kernel's entries, which every process root holds in its kernel slots.
    pub kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>,
}

impl Spaces {
    pub fn new(kernel_entries: Array<usize, KERNEL_MEM_END_L4INDEX>) -> (ret: Self)
        ensures
            ret.kernel_entries == kernel_entries,
            ret.roots@ == Map::<usize, PointsTo<PageMap>>::empty(),
            ret.records@ == Map::<usize, PointsTo<SpaceRecord>>::empty(),
            ret.loaded@ == Map::<usize, PointsTo<SpaceCores>>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
            ret.bound@ == IMap::<usize, Set<usize>>::empty(),
    {
        Spaces {
            roots: Tracked(Map::tracked_empty()),
            records: Tracked(Map::tracked_empty()),
            loaded: Tracked(Map::tracked_empty()),
            holders: Ghost(IMap::empty()),
            bound: Ghost(IMap::empty()),
            kernel_entries,
        }
    }
}

/// The block at page b holds a space.
pub open spec fn space_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is Space
}

/// The space at s has its record, the root table its record points at and its list of cores. A device
/// space is a block of its own with node pages, whose references are exactly its holders and the
/// devices bound to it, and it is dead at once when they go. A process space lies in its process's
/// block, which its process capabilities hold, so no space capability names it and no device is bound
/// to it.
pub open spec fn space_wf(list: &Tree, spaces: &Spaces, blocks: &BlockTable, s: usize) -> bool {
    &&& s % 32768 == 0
    &&& blocks.tracks_addr(s)
    &&& spaces.records@.contains_key(s)
    &&& spaces.records@[s].addr() == s + SPACE_RECORD_PAGE * 4096
    &&& spaces.records@[s].is_init()
    &&& spaces.records@[s].value().root == s + SPACE_ROOT_PAGE * 4096
    &&& root_record_wf(spaces, s)
    &&& spaces.roots@[s].addr() == spaces.records@[s].value().root
    &&& spaces.roots@[s].is_init()
    &&& spaces.roots@[s].value().wf()
    &&& spaces.loaded@.contains_key(s)
    &&& spaces.loaded@[s].addr() == s + SPACE_CORES_PAGE * 4096
    &&& spaces.loaded@[s].is_init()
    &&& spaces.records@[s].value().kind is Device ==> spaces.loaded@[s].value().list == 0u32
    &&& blocks.pages@[(s / 4096) as int].kind is Base
    &&& spaces.records@[s].value().kind is Device ==> blocks.pages@[(s / 4096) as int].object is Space
    &&& spaces.records@[s].value().kind is Process ==> blocks.pages@[(s / 4096) as int].object is Process
    &&& blocks.pages@[(s / 4096) as int].order == 3
    &&& spaces.records@[s].value().kind is Device
        ==> forall|k: usize| k < TABLE_NODE_PAGES ==> list.pages@.dom().contains(#[trigger] table_node_page(s, k))
    &&& spaces.holders@.contains_key(s)
    &&& kernel_slots_wf(spaces, s)
    &&& spaces.holders@[s].finite()
    &&& spaces.bound@.contains_key(s)
    &&& spaces.bound@[s].finite()
    &&& spaces.records@[s].value().kind is Process ==> spaces.bound@[s] == Set::<usize>::empty()
    &&& spaces.records@[s].value().kind is Process ==> spaces.holders@[s] == Set::<usize>::empty()
    &&& spaces.records@[s].value().kind is Device
        ==> spaces.holders@[s].len() + spaces.bound@[s].len() == blocks.pages@[(s / 4096) as int].refs
    &&& spaces.records@[s].value().kind is Device
        ==> (blocks.pages@[(s / 4096) as int].refs == 0 ==> blocks.pages@[(s / 4096) as int].dead)
}

/// Entry i of a root of this kind holds the kernel's. Kernel slots exist only in process spaces.
pub open spec fn holds_kernel(kind: SpaceKind, i: usize) -> bool {
    kind is Process && i < KERNEL_MEM_END_L4INDEX
}

/// A root is level 4, of its own space, with no parent. A root not written has no entry but the kernel
/// slots, and any entry outside them is present or empty.
pub open spec fn root_record_wf(spaces: &Spaces, s: usize) -> bool {
    let record = spaces.records@[s].value().table;
    &&& record.level == 4
    &&& spaces.roots@[s].value().level@ == 4
    &&& record.space == Some(s)
    &&& record.parent is None
    &&& !record.written ==> forall|i: usize| #![trigger spaces.roots@[s].value()[i]]
        i < 512 && !holds_kernel(spaces.records@[s].value().kind, i) ==> spaces.roots@[s].value()[i].is_empty()
    &&& forall|i: usize| #![trigger spaces.roots@[s].value()[i]]
        i < 512 && !holds_kernel(spaces.records@[s].value().kind, i)
            ==> spaces.roots@[s].value()[i].perm.present || spaces.roots@[s].value()[i].is_empty()
}

/// A process root holds the kernel's entries in the kernel slots, so the kernel stays mapped on entry
/// from user mode. The same entries of a device root are empty or name a child table.
pub open spec fn kernel_slots_wf(spaces: &Spaces, s: usize) -> bool {
    forall|i: usize| #![trigger spaces.roots@[s].value()[i]] i < KERNEL_MEM_END_L4INDEX ==> match spaces.records@[s].value().kind {
        SpaceKind::Process => spaces.roots@[s].value()[i] == usize2page_entry(spaces.kernel_entries@[i as int], 4),
        SpaceKind::Device => spaces.roots@[s].value()[i].is_empty()
            || (spaces.roots@[s].value()[i].perm.present && !spaces.roots@[s].value()[i].perm.ps),
    }
}

/// Each space is well formed, a space's block is one of these, and the capabilities of kind Space are
/// exactly the holders.
pub open spec fn spaces_wf(list: &Tree, tables: &Tables, spaces: &Spaces, blocks: &BlockTable) -> bool {
    &&& spaces.kernel_entries.wf()
    &&& forall|s: usize| #[trigger] spaces.roots@.contains_key(s) ==> space_wf(list, spaces, blocks, s)
    &&& forall|s: usize| #[trigger] spaces.loaded@.contains_key(s) ==> spaces.roots@.contains_key(s)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] space_block(blocks, b)
        ==> spaces.roots@.contains_key((b * 4096) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Space ==> {
        &&& spaces.roots@.contains_key(tables.payload_of(n).base)
        &&& spaces.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == 3
    }
    &&& forall|s: usize, n: usize| spaces.roots@.contains_key(s) && #[trigger] spaces.holders@[s].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Space
        &&& tables.payload_of(n).base == s
    }
}

/// Each space's holders after node i is renamed n.
pub open spec fn moved_space_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |s: usize| holders.contains_key(s),
        |s: usize| if holders[s].contains(i) { holders[s].remove(i).insert(n) } else { holders[s] },
    )
}

/// The space capabilities of a and b are the same, saying the same.
pub open spec fn same_spaces(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Space ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Space ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The spaces read nothing of the list but its pages, and nothing of the capabilities but the spaces.
pub proof fn lemma_spaces_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    spaces: &Spaces,
    blocks: &BlockTable,
)
    requires
        spaces_wf(list_a, tables_a, spaces, blocks),
        same_spaces(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        spaces_wf(list_b, tables_b, spaces, blocks),
{
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) implies space_wf(list_b, spaces, blocks, s) by {
        assert(space_wf(list_a, spaces, blocks, s));
        if spaces.records@[s].value().kind is Device {
            assert forall|k: usize| k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
                assert(list_a.pages@.dom().contains(table_node_page(s, k)));
            }
        }
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Space implies {
        &&& spaces.roots@.contains_key(tables_b.payload_of(n).base)
        &&& spaces.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 3
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|s: usize, n: usize| spaces.roots@.contains_key(s) && #[trigger] spaces.holders@[s].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Space
        &&& tables_b.payload_of(n).base == s
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_spaces_same_pages(list: &Tree, tables: &Tables, spaces: &Spaces, a: &BlockTable, b: &BlockTable)
    requires
        spaces_wf(list, tables, spaces, a),
        b.pages@ == a.pages@,
    ensures
        spaces_wf(list, tables, spaces, b),
{
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) implies space_wf(list, spaces, b, s) by {
        assert(space_wf(list, spaces, a, s));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies spaces.roots@.contains_key((x * 4096) as usize) by {
        assert(space_block(a, x));
    }
}

/// A step that changes the count of a block that is no space's leaves every space's block as it was.
pub proof fn lemma_spaces_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    spaces: &Spaces,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        spaces_wf(list_a, tables_a, spaces, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is Space),
            _ => true,
        },
        same_spaces(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        spaces_wf(list_b, tables_b, spaces, b),
{
    lemma_spaces_same_caps(list_a, tables_a, list_b, tables_b, spaces, a);
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) implies space_wf(list_b, spaces, b, s) by {
        assert(space_wf(list_b, spaces, a, s));
        if spaces.records@[s].value().kind is Device {
            let x = BlockRef::Small(s / 4096);
            assert(block_typed(a, x));
            assert(x != br);
            assert(block_refs(b, x) == block_refs(a, x));
            assert(block_dead(b, x) == block_dead(a, x));
        }
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies spaces.roots@.contains_key((x * 4096) as usize) by {
        assert(space_block(a, x));
    }
}

/// The spaces after a free small block is typed as something that is no space: no space lay in it,
/// and a space block outside it was one before.
pub proof fn lemma_spaces_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    spaces: &Spaces,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        spaces_wf(list_a, tables_a, spaces, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !((#[trigger] b.pages@[base + k]).object is Space),
        same_spaces(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        spaces_wf(list_b, tables_b, spaces, b),
{
    lemma_spaces_same_caps(list_a, tables_a, list_b, tables_b, spaces, a);
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) implies space_wf(list_b, spaces, b, s) by {
        assert(space_wf(list_b, spaces, a, s));
        let x = (s / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies spaces.roots@.contains_key((x * 4096) as usize) by {
        if base <= x < base + size {
            assert(!(b.pages@[base + (x - base)].object is Space));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(space_block(a, x));
    }
}

/// The spaces after a small block frees: a space's first page is the list's, so it was not in it, and
/// a freed page is no space block.
pub proof fn lemma_spaces_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    spaces: &Spaces,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        spaces_wf(list_a, tables_a, spaces, a),
        a.wf(),
        a.tracks(base as int),
        a.pages@[base as int].kind is Base,
        !(a.pages@[base as int].object is Process),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && a.tracks_addr(p)
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_spaces(list_a, tables_a, list_b, tables_b),
        forall|s: usize, k: usize| #[trigger] spaces.roots@.contains_key(s) && spaces.records@[s].value().kind is Device
            && k < TABLE_NODE_PAGES ==> list_b.pages@.dom().contains(#[trigger] table_node_page(s, k)),
    ensures
        spaces_wf(list_b, tables_b, spaces, b),
{
    lemma_process_spaces_outside_block(list_a, tables_a, spaces, a, base);
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) implies space_wf(list_b, spaces, b, s) by {
        assert(space_wf(list_a, spaces, a, s));
        if spaces.records@[s].value().kind is Device {
            assert(list_b.pages@.dom().contains(table_node_page(s, 0)));
            assert(table_node_page(s, 0) == s);
        }
        assert(!a.in_block(base as int, (s / 4096) as int));
        assert(b.pages@[(s / 4096) as int] == a.pages@[(s / 4096) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies spaces.roots@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(space_block(a, x));
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Space implies {
        &&& spaces.roots@.contains_key(tables_b.payload_of(n).base)
        &&& spaces.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 3
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|s: usize, n: usize| spaces.roots@.contains_key(s) && #[trigger] spaces.holders@[s].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Space
        &&& tables_b.payload_of(n).base == s
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// No process's space lies in a block that is no process's: a process space's first page is its
/// process's base.
pub proof fn lemma_process_spaces_outside_block(list: &Tree, tables: &Tables, spaces: &Spaces, blocks: &BlockTable, page: usize)
    requires
        spaces_wf(list, tables, spaces, blocks),
        blocks.wf(),
        blocks.tracks(page as int),
        blocks.pages@[page as int].kind is Base,
        !(blocks.pages@[page as int].object is Process),
    ensures
        forall|s: usize| #[trigger] spaces.roots@.contains_key(s) && spaces.records@[s].value().kind is Process
            ==> !blocks.in_block(page as int, (s / 4096) as int),
{
    assert forall|s: usize| #[trigger] spaces.roots@.contains_key(s) && spaces.records@[s].value().kind is Process
        implies !blocks.in_block(page as int, (s / 4096) as int) by {
        assert(space_wf(list, spaces, blocks, s));
        let x = (s / 4096) as int;
        if blocks.in_block(page as int, x) && x != page {
            blocks.lemma_member_of(page as int, x);
        }
    }
}

/// A device space's node pages stay the list's when a page of another kind of block leaves it: each is
/// its block's base or member.
pub proof fn lemma_space_node_pages_kept(
    list_a: &Tree,
    list_b: &Tree,
    tables: &Tables,
    spaces: &Spaces,
    blocks: &BlockTable,
    base: usize,
)
    requires
        spaces_wf(list_a, tables, spaces, blocks),
        blocks.wf(),
        blocks.tracks_addr(base),
        !(blocks.pages@[(base / 4096) as int].kind is Member),
        !(blocks.pages@[(base / 4096) as int].object is Space),
        list_b.pages@.dom() == list_a.pages@.dom().remove(base),
    ensures
        forall|s: usize, k: usize| #[trigger] spaces.roots@.contains_key(s) && spaces.records@[s].value().kind is Device
            && k < TABLE_NODE_PAGES ==> list_b.pages@.dom().contains(#[trigger] table_node_page(s, k)),
{
    assert forall|s: usize, k: usize| #[trigger] spaces.roots@.contains_key(s) && spaces.records@[s].value().kind is Device
        && k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
        assert(space_wf(list_a, spaces, blocks, s));
        let p = table_node_page(s, k);
        assert(list_a.pages@.dom().contains(p));
        let page = (s / 4096) as int;
        blocks.lemma_base(page);
        lemma_table_node_page(s, k);
        if k == 0 {
            assert(p / 4096 == s / 4096);
        } else {
            blocks.lemma_member_of(page, page + k);
        }
        assert(p / 4096 != base / 4096);
    }
}

/// Adds the five node pages at the start of the block at base to the list.
fn add_node_pages(
    list: &mut Tree,
    base: usize,
    Tracked(p0): Tracked<PagePerm4k>,
    Tracked(p1): Tracked<PagePerm4k>,
    Tracked(p2): Tracked<PagePerm4k>,
    Tracked(p3): Tracked<PagePerm4k>,
    Tracked(p4): Tracked<PagePerm4k>,
)
    requires
        old(list).wf(),
        base % 32768 == 0,
        base + 32768 <= NODE_SPACE,
        base / 4096 + 8 <= NUM_PAGES,
        p0.addr() == base,
        p1.addr() == base + 4096,
        p2.addr() == base + 2 * 4096,
        p3.addr() == base + 3 * 4096,
        p4.addr() == base + 4 * 4096,
        forall|k: usize| k < TABLE_NODE_PAGES ==> !old(list).pages@.dom().contains(#[trigger] table_node_page(base, k)),
    ensures
        final(list).wf(),
        list_grown(*old(list), *final(list)),
        final(list).valid(base),
        !final(list).nodes@[base as int].live,
        forall|k: usize| k < TABLE_NODE_PAGES ==> final(list).pages@.dom().contains(#[trigger] table_node_page(base, k)),
        forall|p: usize| #[trigger] final(list).pages@.dom().contains(p) ==> old(list).pages@.dom().contains(p)
            || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
{
    let ghost l0 = *list;
    proof {
        assert forall|k: usize| k < TABLE_NODE_PAGES implies #[trigger] table_node_page(base, k) == base + k * 4096
            && table_node_page(base, k) % 4096 == 0 by {
            lemma_table_node_page(base, k);
        }
        assert(table_node_page(base, 0) == base);
        assert(table_node_page(base, 1) == base + 4096);
        assert(table_node_page(base, 2) == base + 2 * 4096);
        assert(table_node_page(base, 3) == base + 3 * 4096);
        assert(table_node_page(base, 4) == base + 4 * 4096);
    }
    let nodes = init_node_page(base, Tracked(p0));
    list.add_page(base, nodes);
    let ghost l1 = *list;
    let nodes = init_node_page(base + 4096, Tracked(p1));
    proof {
        assert(list_grown(l0, l1));
        assert(l1.valid(base));
        assert(!l1.nodes@[base as int].live);
    }
    list.add_page(base + 4096, nodes);
    let ghost l2 = *list;
    let nodes = init_node_page(base + 2 * 4096, Tracked(p2));
    proof {
        assert(list_grown(l1, l2));
        lemma_list_grown_trans(l0, l1, l2);
    }
    list.add_page(base + 2 * 4096, nodes);
    let ghost l3 = *list;
    let nodes = init_node_page(base + 3 * 4096, Tracked(p3));
    proof {
        assert(list_grown(l2, l3));
        lemma_list_grown_trans(l0, l2, l3);
    }
    list.add_page(base + 3 * 4096, nodes);
    let ghost l4 = *list;
    let nodes = init_node_page(base + 4 * 4096, Tracked(p4));
    proof {
        assert(list_grown(l3, l4));
        lemma_list_grown_trans(l0, l3, l4);
    }
    list.add_page(base + 4 * 4096, nodes);
    proof {
        let l5 = *list;
        assert(list_grown(l4, l5));
        lemma_list_grown_trans(l0, l4, l5);
        assert(l5.valid(base) && !l5.nodes@[base as int].live);
        assert forall|p: usize| #[trigger] l5.pages@.dom().contains(p) implies l0.pages@.dom().contains(p)
            || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k) by {
            if !l0.pages@.dom().contains(p) {
                if p == base {
                    assert(p == table_node_page(base, 0));
                } else if p == base + 4096 {
                    assert(p == table_node_page(base, 1));
                } else if p == base + 2 * 4096 {
                    assert(p == table_node_page(base, 2));
                } else if p == base + 3 * 4096 {
                    assert(p == table_node_page(base, 3));
                } else {
                    assert(p == table_node_page(base, 4));
                }
            }
        }
        assert forall|k: usize| k < TABLE_NODE_PAGES implies l5.pages@.dom().contains(#[trigger] table_node_page(base, k)) by {
            if k == 0 {
                assert(l5.pages@.dom().contains(base));
            } else if k == 1 {
                assert(l5.pages@.dom().contains((base + 4096) as usize));
            } else if k == 2 {
                assert(l5.pages@.dom().contains((base + 2 * 4096) as usize));
            } else if k == 3 {
                assert(l5.pages@.dom().contains((base + 3 * 4096) as usize));
            } else {
                assert(l5.pages@.dom().contains((base + 4 * 4096) as usize));
            }
        }
    }
}

impl TablePages {
    pub fn new() -> (ret: Self)
        ensures
            ret.maps@ == Map::<usize, PointsTo<PageMap>>::empty(),
            ret.records@ == Map::<usize, PointsTo<TableRecord>>::empty(),
            ret.spare@ == Map::<usize, PagePerm4k>::empty(),
    {
        TablePages { maps: Tracked(Map::tracked_empty()), records: Tracked(Map::tracked_empty()), spare: Tracked(Map::tracked_empty()) }
    }
}

/// The kth node page of the table page at t.
pub open spec fn table_node_page(t: usize, k: usize) -> usize {
    (t + k * 4096) as usize
}

/// The block at page b holds a table page.
pub open spec fn table_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is TablePage
}

/// A table page is level 1 to 3. One not written has every entry empty, and any entry is present or empty.
pub open spec fn table_record_wf(pages: &TablePages, t: usize) -> bool {
    let record = pages.records@[t].value();
    &&& 1 <= record.level <= 3
    &&& pages.maps@[t].value().level@ == record.level
    &&& !record.written ==> forall|i: usize| #![trigger pages.maps@[t].value()[i]]
        i < 512 ==> pages.maps@[t].value()[i].is_empty()
    &&& forall|i: usize| #![trigger pages.maps@[t].value()[i]]
        i < 512 ==> pages.maps@[t].value()[i].perm.present || pages.maps@[t].value()[i].is_empty()
}

/// The table page at t has its table, its record, its spare page and its node pages. Its block holds one
/// reference, its hidden node's, and is dead at once when that goes, by when no entry names it.
pub open spec fn table_page_wf(list: &Tree, pages: &TablePages, blocks: &BlockTable, t: usize) -> bool {
    &&& t % 32768 == 0
    &&& blocks.tracks_addr(t)
    &&& pages.maps@[t].addr() == t + TABLE_NODE_PAGES * 4096
    &&& pages.maps@[t].is_init()
    &&& pages.maps@[t].value().wf()
    &&& pages.records@.contains_key(t)
    &&& pages.records@[t].addr() == t + TABLE_RECORD_PAGE * 4096
    &&& pages.records@[t].is_init()
    &&& table_record_wf(pages, t)
    &&& pages.spare@.contains_key((t + 7 * 4096) as usize)
    &&& pages.spare@[(t + 7 * 4096) as usize].addr() == t + 7 * 4096
    &&& pages.spare@[(t + 7 * 4096) as usize].is_uninit()
    &&& blocks.pages@[(t / 4096) as int].kind is Base
    &&& blocks.pages@[(t / 4096) as int].object is TablePage
    &&& blocks.pages@[(t / 4096) as int].order == 3
    &&& forall|k: usize| k < TABLE_NODE_PAGES ==> list.pages@.dom().contains(#[trigger] table_node_page(t, k))
    &&& list.nodes@[t as int].live ==> {
        &&& list.nodes@[t as int].kind is Hidden
        &&& blocks.pages@[(t / 4096) as int].refs == 1
        &&& !blocks.pages@[(t / 4096) as int].dead
    }
    &&& !list.nodes@[t as int].live ==> {
        &&& blocks.pages@[(t / 4096) as int].refs == 0
        &&& blocks.pages@[(t / 4096) as int].dead
        &&& pages.records@[t].value().parent is None
    }
}

/// Each table page is well formed, and a table page block is one of these, so a retype naming one
/// finds its node.
pub open spec fn table_pages_wf(list: &Tree, pages: &TablePages, blocks: &BlockTable) -> bool {
    &&& forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> table_page_wf(list, pages, blocks, t)
    &&& forall|b: usize| blocks.tracks(b as int) && #[trigger] table_block(blocks, b)
        ==> pages.maps@.contains_key((b * 4096) as usize)
}

/// Every table page's node is as it was.
pub open spec fn same_table_nodes(list_a: &Tree, list_b: &Tree, pages: &TablePages) -> bool {
    forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> {
        &&& list_b.nodes@[t as int].live == list_a.nodes@[t as int].live
        &&& list_b.nodes@[t as int].kind == list_a.nodes@[t as int].kind
    }
}

/// A table page's base, eight pages aligned, is page aligned and is its page's base.
pub proof fn lemma_table_page_aligned(t: usize)
    requires
        t % 32768 == 0,
    ensures
        t % 4096 == 0,
        t as int == 4096 * (t as int / 4096),
        (t / 4096) % 8 == 0,
{
    lemma_fundamental_div_mod(t as int, 32768);
    let q = t as int / 32768;
    assert(t as int == 4096 * (8 * q));
    lemma_mod_multiples_basic(8 * q, 4096);
    lemma_div_multiples_vanish(8 * q, 4096);
    assert(t as int / 4096 == 8 * q);
    lemma_mod_multiples_basic(q, 8);
}

/// Two distinct table pages lie on distinct pages.
pub proof fn lemma_table_pages_distinct(t: usize, u: usize)
    requires
        t % 32768 == 0,
        u % 32768 == 0,
        t != u,
    ensures
        t / 4096 != u / 4096,
{
    lemma_table_page_aligned(t);
    lemma_table_page_aligned(u);
}

/// The kth node page of a table page is the kth page of its block, page aligned.
pub proof fn lemma_table_node_page(t: usize, k: usize)
    requires
        t % 32768 == 0,
        t / 4096 + k < NUM_PAGES,
    ensures
        table_node_page(t, k) == t + k * 4096,
        table_node_page(t, k) % 4096 == 0,
        table_node_page(t, k) / 4096 == t / 4096 + k,
{
    lemma_table_page_aligned(t);
    let p = t as int / 4096;
    assert((t + k * 4096) as int == 4096 * (p + k));
    lemma_mod_multiples_basic(p + k, 4096);
    lemma_div_multiples_vanish(p + k, 4096);
}

/// A node page of one table page or space lies outside the node pages of any other: the blocks are
/// eight pages apart and a block's node pages are its first five.
pub proof fn lemma_node_pages_disjoint(t: usize, u: usize, k: usize)
    requires
        t % 32768 == 0,
        u % 32768 == 0,
        t != u,
        t / 4096 < NUM_PAGES,
        k < TABLE_NODE_PAGES,
    ensures
        !(u <= table_node_page(t, k) < u + TABLE_NODE_PAGES * 4096),
{
    lemma_table_bound(t);
    assert(table_node_page(t, k) == t + k * 4096);
    lemma_fundamental_div_mod(t as int, 32768);
    lemma_fundamental_div_mod(u as int, 32768);
    let qt = t as int / 32768;
    let qu = u as int / 32768;
    assert(t as int == 32768 * qt);
    assert(u as int == 32768 * qu);
    if qt < qu {
        assert(32768 * qt + 32768 <= 32768 * qu);
    } else {
        assert(32768 * qu + 32768 <= 32768 * qt);
    }
}

/// A page that is a node page of both the table page or space at `t` and the one at `u` makes them one:
/// the blocks are eight pages apart and a block's node pages are its first five.
pub proof fn lemma_node_page_names_block(t: usize, u: usize, p: usize)
    requires
        t % 32768 == 0,
        u % 32768 == 0,
        t / 4096 <= p < t / 4096 + TABLE_NODE_PAGES,
        u / 4096 <= p < u / 4096 + TABLE_NODE_PAGES,
    ensures
        t == u,
{
    lemma_table_page_aligned(t);
    lemma_table_page_aligned(u);
    let a = t as int / 4096;
    let b = u as int / 4096;
    lemma_fundamental_div_mod(a, 8);
    lemma_fundamental_div_mod(b, 8);
    let qa = a / 8;
    let qb = b / 8;
    assert(a == 8 * qa);
    assert(b == 8 * qb);
    if qa < qb {
        assert(8 * qa + 8 <= 8 * qb);
        assert(false);
    } else if qb < qa {
        assert(8 * qb + 8 <= 8 * qa);
        assert(false);
    }
    assert(a == b);
    assert(t as int == 4096 * a);
    assert(u as int == 4096 * b);
}

/// The block at `base`, eight pages aligned, starts at `page`.
pub proof fn lemma_table_page_base(base: usize, page: usize)
    requires
        base % 32768 == 0,
        page == base / 4096,
    ensures
        page % 8 == 0,
        page * 4096 == base,
        base % 4096 == 0,
{
    lemma_table_page_aligned(base);
}

/// The table pages read nothing of the list but their node pages and nodes.
pub proof fn lemma_table_pages_same_nodes(list_a: &Tree, list_b: &Tree, pages: &TablePages, blocks: &BlockTable)
    requires
        table_pages_wf(list_a, pages, blocks),
        same_table_nodes(list_a, list_b, pages),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, blocks),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, blocks, t) by {
        assert(table_page_wf(list_a, pages, blocks, t));
        assert forall|k: usize| k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
            assert(list_a.pages@.dom().contains(table_node_page(t, k)));
        }
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_table_pages_same_pages(list: &Tree, pages: &TablePages, a: &BlockTable, b: &BlockTable)
    requires
        table_pages_wf(list, pages, a),
        b.pages@ == a.pages@,
    ensures
        table_pages_wf(list, pages, b),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list, pages, b, t) by {
        assert(table_page_wf(list, pages, a, t));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// A table page's block is no holder's key: a holder's small block is a frame.
pub proof fn lemma_table_page_unkeyed(
    list: &Tree,
    pages: &TablePages,
    tables: &Tables,
    blocks: &BlockTable,
    holders: IMap<BlockRef, Set<usize>>,
    t: usize,
)
    requires
        table_pages_wf(list, pages, blocks),
        objects_wf(tables, blocks, holders),
        pages.maps@.contains_key(t),
    ensures
        blocks.tracks_addr(t),
        block_typed(blocks, BlockRef::Small(t / 4096)),
        !holders.contains_key(BlockRef::Small(t / 4096)),
{
    assert(table_page_wf(list, pages, blocks, t));
    if holders.contains_key(BlockRef::Small(t / 4096)) {
        assert(blocks.pages@[(t / 4096) as int].object is Frame);
    }
}

/// A step that changes the count of a block that is no table page's leaves every table page's block
/// as it was.
pub proof fn lemma_table_pages_refs_changed(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        table_pages_wf(list_a, pages, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is TablePage),
            _ => true,
        },
        same_table_nodes(list_a, list_b, pages),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, b),
{
    lemma_table_pages_same_nodes(list_a, list_b, pages, a);
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, b, t) by {
        assert(table_page_wf(list_b, pages, a, t));
        let x = BlockRef::Small(t / 4096);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// The table pages after hidden node t goes and its block's one reference with it: that block is dead
/// at zero, and every other table page's block is as it was, since no two lie on one page.
pub proof fn lemma_table_page_dropped(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    t: usize,
)
    requires
        table_pages_wf(list_a, pages, a),
        pages.maps@.contains_key(t),
        pages.records@[t].value().parent is None,
        blocks_refs_changed(a, b, BlockRef::Small(t / 4096), 0, true),
        !list_b.nodes@[t as int].live,
        forall|u: usize| #[trigger] pages.maps@.contains_key(u) && u != t ==> {
            &&& list_b.nodes@[u as int].live == list_a.nodes@[u as int].live
            &&& list_b.nodes@[u as int].kind == list_a.nodes@[u as int].kind
        },
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        table_pages_wf(list_b, pages, b),
{
    let br = BlockRef::Small(t / 4096);
    assert forall|u: usize| #[trigger] pages.maps@.contains_key(u) implies table_page_wf(list_b, pages, b, u) by {
        assert(table_page_wf(list_a, pages, a, u));
        assert forall|k: usize| k < TABLE_NODE_PAGES implies list_b.pages@.dom().contains(#[trigger] table_node_page(u, k)) by {
            assert(list_a.pages@.dom().contains(table_node_page(u, k)));
        }
        if u != t {
            lemma_table_pages_distinct(u, t);
            let x = BlockRef::Small(u / 4096);
            assert(block_typed(a, x));
            assert(x != br);
            assert(block_refs(b, x) == block_refs(a, x));
            assert(block_dead(b, x) == block_dead(a, x));
        }
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(table_block(a, x));
    }
}

/// The table pages after a free small block is typed: no table page lay in it, and a table block
/// outside it was one before.
pub proof fn lemma_table_pages_small_typed(
    list: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        table_pages_wf(list, pages, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
    ensures
        forall|t: usize| #[trigger] pages.maps@.contains_key(t) ==> table_page_wf(list, pages, b, t),
        forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) && !(base <= x < base + size)
            ==> pages.maps@.contains_key((x * 4096) as usize),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list, pages, b, t) by {
        assert(table_page_wf(list, pages, a, t));
        let x = (t / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) && !(base <= x < base + size)
        implies pages.maps@.contains_key((x * 4096) as usize) by {
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(table_block(a, x));
    }
}

/// The spaces after one with no holder frees its block: every other space's first page is the list's, so
/// it was not in the block, a freed page is no space block, and no capability names the space that went.
pub proof fn lemma_spaces_space_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    sa: &Spaces,
    sb: &Spaces,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        spaces_wf(list_a, tables_a, sa, a),
        sa.roots@.contains_key(base),
        sa.holders@[base] == Set::<usize>::empty(),
        sb.roots@ == sa.roots@.remove(base),
        sb.records@ == sa.records@.remove(base),
        sb.loaded@ == sa.loaded@.remove(base),
        sb.holders@ == sa.holders@.remove(base),
        sb.bound@ == sa.bound@.remove(base),
        sb.kernel_entries == sa.kernel_entries,
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && a.tracks_addr(p)
            ==> !a.in_block((base / 4096) as int, (p / 4096) as int),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block((base / 4096) as int, i) { free_entry() } else { a.pages@[i] }),
        same_spaces(list_a, tables_a, list_b, tables_b),
        a.wf(),
        a.tracks_addr(base),
        a.pages@[(base / 4096) as int].kind is Base,
        a.pages@[(base / 4096) as int].object is Space || a.pages@[(base / 4096) as int].object is Process,
        forall|s: usize, k: usize| #[trigger] sb.roots@.contains_key(s) && sb.records@[s].value().kind is Device
            && k < TABLE_NODE_PAGES ==> list_b.pages@.dom().contains(#[trigger] table_node_page(s, k)),
    ensures
        spaces_wf(list_b, tables_b, sb, b),
{
    let page = base / 4096;
    assert(space_wf(list_a, sa, a, base));
    lemma_table_page_aligned(base);
    assert forall|s: usize| #[trigger] sb.roots@.contains_key(s) implies space_wf(list_b, sb, b, s) by {
        assert(sa.roots@.contains_key(s));
        assert(space_wf(list_a, sa, a, s));
        assert(sb.records@[s] == sa.records@[s]);
        lemma_table_page_aligned(s);
        let x = (s / 4096) as int;
        if a.in_block(page as int, x) && x != page {
            a.lemma_member_of(page as int, x);
        }
        assert(!a.in_block(page as int, (s / 4096) as int));
        assert(b.pages@[(s / 4096) as int] == a.pages@[(s / 4096) as int]);
        assert(sb.records@[s] == sa.records@[s]);
        assert(sb.roots@[s] == sa.roots@[s]);
        assert(sb.loaded@[s] == sa.loaded@[s]);
        assert(sb.holders@[s] == sa.holders@[s]);
        assert(sb.bound@[s] == sa.bound@[s]);
        assert(root_record_wf(sb, s)) by {
            assert(root_record_wf(sa, s));
        }
        assert(kernel_slots_wf(sb, s)) by {
            assert(kernel_slots_wf(sa, s));
        }
    }
    assert forall|s: usize| #[trigger] sb.loaded@.contains_key(s) implies sb.roots@.contains_key(s) by {
        assert(sa.loaded@.contains_key(s));
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies sb.roots@.contains_key((x * 4096) as usize) by {
        if a.in_block(page as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(space_block(a, x));
        assert(x != page);
        assert(((x * 4096) as usize) / 4096 == x);
        assert((x * 4096) as usize != base);
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Space implies {
        &&& sb.roots@.contains_key(tables_b.payload_of(n).base)
        &&& sb.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == 3
    } by {
        assert(tables_a.is_cap(list_a, n));
        assert(sa.holders@[tables_a.payload_of(n).base].contains(n));
        assert(tables_a.payload_of(n).base != base);
    }
    assert forall|s: usize, n: usize| sb.roots@.contains_key(s) && #[trigger] sb.holders@[s].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Space
        &&& tables_b.payload_of(n).base == s
    } by {
        assert(sb.holders@[s] == sa.holders@[s]);
        assert(sa.holders@[s].contains(n));
        assert(tables_a.is_cap(list_a, n));
    }
}

/// The table pages after a small block frees: a table page's first page is the list's, so it was not
/// in it, and a freed page is no table block.
pub proof fn lemma_table_pages_small_freed(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        table_pages_wf(list_a, pages, a),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && a.tracks_addr(p)
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_table_nodes(list_a, list_b, pages),
        forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            ==> list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)),
    ensures
        table_pages_wf(list_b, pages, b),
{
    assert forall|t: usize| #[trigger] pages.maps@.contains_key(t) implies table_page_wf(list_b, pages, b, t) by {
        assert(table_page_wf(list_a, pages, a, t));
        assert(list_b.pages@.dom().contains(table_node_page(t, 0)));
        assert(table_node_page(t, 0) == t);
        assert(!a.in_block(base as int, (t / 4096) as int));
        assert(b.pages@[(t / 4096) as int] == a.pages@[(t / 4096) as int]);
    }
    assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) implies pages.maps@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(table_block(a, x));
    }
}

/// A table page's node pages stay the list's when a page of another kind of block leaves it: each is
/// its block's base or member.
pub proof fn lemma_table_node_pages_kept(
    list_a: &Tree,
    list_b: &Tree,
    pages: &TablePages,
    blocks: &BlockTable,
    base: usize,
)
    requires
        table_pages_wf(list_a, pages, blocks),
        blocks.wf(),
        blocks.tracks_addr(base),
        !(blocks.pages@[(base / 4096) as int].kind is Member),
        !(blocks.pages@[(base / 4096) as int].object is TablePage),
        list_b.pages@.dom() == list_a.pages@.dom().remove(base),
    ensures
        forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
            ==> list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)),
{
    assert forall|t: usize, k: usize| #[trigger] pages.maps@.contains_key(t) && k < TABLE_NODE_PAGES
        implies list_b.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
        assert(table_page_wf(list_a, pages, blocks, t));
        let p = table_node_page(t, k);
        assert(list_a.pages@.dom().contains(p));
        let page = (t / 4096) as int;
        blocks.lemma_base(page);
        lemma_table_node_page(t, k);
        if k == 0 {
            assert(p / 4096 == t / 4096);
        } else {
            blocks.lemma_member_of(page, page + k);
        }
        assert(p / 4096 != base / 4096);
    }
}

/// The list's pages stay used after a free small block is typed: none lay in it, and a member page's
/// base is a base, so not in it either.
pub proof fn lemma_list_pages_used_small_typed(list: &Tree, a: &BlockTable, b: &BlockTable, base: usize, size: int)
    requires
        list_pages_used(list, a),
        a.member_bases_wf(),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| a.tracks(i) && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && b.tracks_addr(p) implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& b.pages@[(p / 4096) as int].kind is Member
            ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
                || b.pages@[b.pages@[(p / 4096) as int].base as int].object is Space
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        let x = (p / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
        if a.pages@[x].kind is Member {
            a.lemma_member(x);
            let bb = a.pages@[x].base as int;
            if base <= bb < base + size {
                assert(a.pages@[base + (bb - base)].kind is Free);
            }
            assert(b.pages@[bb] == a.pages@[bb]);
        }
    }
}

/// The list's pages stay used after a small block frees: none lay in it, and a member page's base is
/// a base in the same block, so not in it either.
pub proof fn lemma_list_pages_used_small_freed(list: &Tree, a: &BlockTable, b: &BlockTable, base: usize)
    requires
        list_pages_used(list, a),
        a.wf(),
        a.tracks(base as int),
        a.pages@[base as int].kind is Base,
        forall|p: usize| #[trigger] list.pages@.dom().contains(p) && a.tracks_addr(p)
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| a.tracks(i) ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
    ensures
        list_pages_used(list, b),
{
    assert forall|p: usize| #[trigger] list.pages@.dom().contains(p) && b.tracks_addr(p) implies {
        &&& !(b.pages@[(p / 4096) as int].kind is Free)
        &&& b.pages@[(p / 4096) as int].kind is Member
            ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
                || b.pages@[b.pages@[(p / 4096) as int].base as int].object is Space
        &&& !(b.pages@[(p / 4096) as int].object is Frame)
    } by {
        let x = (p / 4096) as int;
        assert(!a.in_block(base as int, x));
        assert(b.pages@[x] == a.pages@[x]);
        if a.pages@[x].kind is Member {
            a.lemma_member(x);
            let bb = a.pages@[x].base as int;
            if a.in_block(base as int, bb) {
                if bb != base as int {
                    a.lemma_member_of(base as int, bb);
                }
                assert(bb == base as int);
                assert(a.in_block(base as int, x));
            }
            assert(b.pages@[bb] == a.pages@[bb]);
        }
    }
}

/// The list's pages stay used when it gains a page of a typed block that is no frame.
pub proof fn lemma_list_pages_used_page_added(list_a: &Tree, list_b: &Tree, blocks: &BlockTable, p: usize)
    requires
        list_pages_used(list_a, blocks),
        list_b.pages@.dom() == list_a.pages@.dom().insert(p),
        blocks.tracks_addr(p) ==> {
            &&& blocks.pages@[(p / 4096) as int].kind is Base
            &&& !(blocks.pages@[(p / 4096) as int].object is Frame)
        },
    ensures
        list_pages_used(list_b, blocks),
{
    assert forall|q: usize| #[trigger] list_b.pages@.dom().contains(q) && blocks.tracks_addr(q) implies {
        &&& !(blocks.pages@[(q / 4096) as int].kind is Free)
        &&& blocks.pages@[(q / 4096) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is TablePage
                || blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is Space
        &&& !(blocks.pages@[(q / 4096) as int].object is Frame)
    } by {
        if q != p {
            assert(list_a.pages@.dom().contains(q));
        }
    }
}

/// And when it loses pages.
pub proof fn lemma_list_pages_used_subset(list_a: &Tree, list_b: &Tree, blocks: &BlockTable)
    requires
        list_pages_used(list_a, blocks),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) ==> list_a.pages@.dom().contains(p),
    ensures
        list_pages_used(list_b, blocks),
{
    assert forall|q: usize| #[trigger] list_b.pages@.dom().contains(q) && blocks.tracks_addr(q) implies {
        &&& !(blocks.pages@[(q / 4096) as int].kind is Free)
        &&& blocks.pages@[(q / 4096) as int].kind is Member
            ==> blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is TablePage
                || blocks.pages@[blocks.pages@[(q / 4096) as int].base as int].object is Space
        &&& !(blocks.pages@[(q / 4096) as int].object is Frame)
    } by {
        assert(list_a.pages@.dom().contains(q));
    }
}

/// A list that gained pages: nothing it held changed, and no node became live.
pub open spec fn list_grown(a: Tree, b: Tree) -> bool {
    &&& b.seq == a.seq
    &&& b.parent == a.parent
    &&& forall|p: usize| #[trigger] a.pages@.dom().contains(p) ==> b.pages@.dom().contains(p)
    &&& forall|i: usize| #[trigger] a.valid(i) ==> b.valid(i) && b.nodes@[i as int] == a.nodes@[i as int]
    &&& forall|i: int| 0 <= i < NODE_SPACE ==> #[trigger] b.nodes@[i].live == a.nodes@[i].live
}

pub proof fn lemma_list_grown_trans(a: Tree, b: Tree, c: Tree)
    requires
        list_grown(a, b),
        list_grown(b, c),
    ensures
        list_grown(a, c),
{
    assert forall|i: usize| #[trigger] a.valid(i) implies c.valid(i) && c.nodes@[i as int] == a.nodes@[i as int] by {
        assert(b.valid(i));
    }
}

impl CapKernel {
    /// A table page's first node page is the list's, so its node 0 is a node the list holds, and it is
    /// no leaf.
    pub proof fn lemma_table_page_valid(&self, t: usize)
        requires
            self.wf(),
            self.table_pages.maps@.contains_key(t),
        ensures
            t % 4096 == 0,
            t < NODE_SPACE,
            self.list.pages@.dom().contains(t),
            self.list.valid(t),
            !self.tables.owner@.contains_key(t),
    {
        assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, t));
        lemma_table_page_aligned(t);
        assert(self.list.pages@.dom().contains(table_node_page(t, 0)));
        assert(table_node_page(t, 0) == t);
        assert(page_of(t) == t);
    }

    /// A slot's node is no table page, since a table page is page aligned.
    pub proof fn lemma_slot_not_table_page(&self, n: usize)
        requires
            self.wf(),
            n % 4096 != 0,
        ensures
            !self.table_pages.maps@.contains_key(n),
    {
        if self.table_pages.maps@.contains_key(n) {
            self.lemma_table_page_valid(n);
        }
    }

    /// A live node that is not hidden is no table page, since a table page's live node is its hidden one.
    pub proof fn lemma_unhidden_not_table_page(&self, n: usize)
        requires
            self.wf(),
            self.list.nodes@[n as int].live,
            !(self.list.nodes@[n as int].kind is Hidden),
        ensures
            !self.table_pages.maps@.contains_key(n),
    {
        if self.table_pages.maps@.contains_key(n) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, n));
        }
    }

    /// A step that changes no node but n and m, neither a table page, leaves every table page's node as
    /// it was.
    pub proof fn lemma_same_table_nodes(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            !pre.table_pages.maps@.contains_key(n),
            !pre.table_pages.maps@.contains_key(m),
        ensures
            same_table_nodes(&pre.list, &post.list, &pre.table_pages),
    {
        assert forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) implies {
            &&& post.list.nodes@[t as int].live == pre.list.nodes@[t as int].live
            &&& post.list.nodes@[t as int].kind == pre.list.nodes@[t as int].kind
        } by {
            pre.lemma_table_page_valid(t);
            assert(t != n && t != m);
        }
    }

    /// A space capability names a space, whose block holds its reference, lies in no typed region and
    /// so is read as the small block at its base.
    pub proof fn lemma_space_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Space,
        ensures
            self.spaces.roots@.contains_key(self.payload_of(n).base),
            self.spaces.holders@[self.payload_of(n).base].contains(n),
            self.spaces.records@[self.payload_of(n).base].value().kind is Device,
            self.payload_of(n).base % 32768 == 0,
            self.blocks.tracks_addr(self.payload_of(n).base),
            self.blocks.pages@[(self.payload_of(n).base / 4096) as int].object is Space,
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / 4096) == BlockRef::Small(self.payload_of(n).base / 4096),
    {
        let s = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        assert(self.spaces.records@[s].value().kind is Device) by {
            if self.spaces.records@[s].value().kind is Process {
                assert(self.spaces.holders@[s].contains(n));
            }
        }
        if self.spaces.holders@[s].len() == 0 {
            self.spaces.holders@[s].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((s / 4096) as int);
    }

    /// The root of the space at s may go: its block has no reference left, so no capability names it and
    /// no device is bound to it.
    pub open spec fn root_may_go(&self, s: usize) -> bool {
        self.blocks.pages@[(s / 4096) as int].refs == 0
    }

    /// A device bound to a space holds a reference to its block, so the root may not go.
    pub proof fn lemma_bound_keeps_root(&self, s: usize, d: usize)
        requires
            self.wf(),
            self.spaces.roots@.contains_key(s),
            self.spaces.bound@[s].contains(d),
        ensures
            self.blocks.pages@[(s / 4096) as int].refs > 0,
            !self.root_may_go(s),
    {
        assert(space_wf(&self.list, &self.spaces, &self.blocks, s));
        if self.spaces.bound@[s].len() == 0 {
            self.spaces.bound@[s].lemma_len0_is_empty();
        }
    }

    /// The spaces after space capability n, the only capability that changed, joins space s with one
    /// more reference on its block.
    pub proof fn lemma_spaces_holder_added(pre: Self, post: Self, n: usize, s: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            !pre.is_cap(n),
            post.is_cap(n),
            post.payload_of(n).kind is Space,
            post.payload_of(n).base == s,
            post.payload_of(n).order == 3,
            pre.spaces.roots@.contains_key(s),
            pre.spaces.records@[s].value().kind is Device,
            block_refs(&pre.blocks, BlockRef::Small(s / 4096)) < usize::MAX,
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(s / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(s / 4096)) + 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(s / 4096)),
            ),
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.loaded == pre.spaces.loaded,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.bound == pre.spaces.bound,
            post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].insert(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
    {
        let ha = pre.spaces.holders@;
        let hb = post.spaces.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(s / 4096);
        assert(space_wf(&pre.list, &pre.spaces, a, s));
        assert(!ha[s].contains(n));
        vstd::set::lemma_set_insert_len(ha[s], n);
        assert forall|t: usize| #[trigger] post.spaces.roots@.contains_key(t)
            implies space_wf(&post.list, &post.spaces, b, t) by {
            assert(space_wf(&pre.list, &pre.spaces, a, t));
            if pre.spaces.records@[t].value().kind is Device {
                assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                    assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                }
            }
            if t != s {
                assert(hb[t] == ha[t]);
                if pre.spaces.records@[t].value().kind is Device {
                    lemma_table_pages_distinct(t, s);
                    let x = BlockRef::Small(t / 4096);
                    assert(block_typed(a, x));
                    assert(x != br);
                    assert(block_refs(b, x) == block_refs(a, x));
                    assert(block_dead(b, x) == block_dead(a, x));
                }
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x)
            implies post.spaces.roots@.contains_key((x * 4096) as usize) by {
            assert(space_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
            &&& post.spaces.roots@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == 3
        } by {
            if x != n {
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
        assert forall|t: usize, x: usize| post.spaces.roots@.contains_key(t) && #[trigger] hb[t].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Space
            &&& post.tables.payload_of(x).base == t
        } by {
            if !(t == s && x == n) {
                assert(ha[t].contains(x));
                assert(pre.tables.is_cap(&pre.list, x));
                assert(x != n);
            }
        }
    }

    /// The spaces after space capability n, the only capability that changed, leaves space s, taking
    /// its reference on the block with it.
    pub proof fn lemma_spaces_holder_dropped(pre: Self, post: Self, n: usize, s: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            pre.payload_of(n).kind is Space,
            pre.payload_of(n).base == s,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(s / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(s / 4096)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(s / 4096)) || block_refs(&pre.blocks, BlockRef::Small(s / 4096)) == 1,
            ),
            post.spaces.roots == pre.spaces.roots,
            post.spaces.records == pre.spaces.records,
            post.spaces.loaded == pre.spaces.loaded,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            post.spaces.bound == pre.spaces.bound,
            post.spaces.holders@ == pre.spaces.holders@.insert(s, pre.spaces.holders@[s].remove(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
    {
        let ha = pre.spaces.holders@;
        let hb = post.spaces.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(s / 4096);
        pre.lemma_space_cap(n);
        assert(space_wf(&pre.list, &pre.spaces, a, s));
        assert(ha[s].contains(n));
        vstd::set::lemma_set_remove_len(ha[s], n);
        assert forall|t: usize| #[trigger] post.spaces.roots@.contains_key(t)
            implies space_wf(&post.list, &post.spaces, b, t) by {
            assert(space_wf(&pre.list, &pre.spaces, a, t));
            if pre.spaces.records@[t].value().kind is Device {
                assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                    assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                }
            }
            if t != s {
                assert(hb[t] == ha[t]);
                if pre.spaces.records@[t].value().kind is Device {
                    lemma_table_pages_distinct(t, s);
                    let x = BlockRef::Small(t / 4096);
                    assert(block_typed(a, x));
                    assert(x != br);
                    assert(block_refs(b, x) == block_refs(a, x));
                    assert(block_dead(b, x) == block_dead(a, x));
                }
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x)
            implies post.spaces.roots@.contains_key((x * 4096) as usize) by {
            assert(space_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
            &&& post.spaces.roots@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == 3
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|t: usize, x: usize| post.spaces.roots@.contains_key(t) && #[trigger] hb[t].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Space
            &&& post.tables.payload_of(x).base == t
        } by {
            assert(ha[t].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// The view after a hidden node joins under a capability: every capability is as it was, and the
    /// only new parent entry is the hidden node's, which no capability descends from.
    pub proof fn lemma_hidden_added_discharges(pre: Self, post: Self, root: usize, parent: usize, n: usize)
        requires
            pre.wf(),
            n < NODE_SPACE,
            !pre.list.nodes@[n as int].live,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> {
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.tables.owner@[page_of(x)] == pre.tables.owner@[page_of(x)]
            },
            post.list.parent@ == pre.list.parent@.insert(n, parent),
            pre.view().holds_right(root, parent, Right::Retype),
        ensures
            discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: n, into: None }),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let f = |x: NodeId| x;
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1) == pre.is_cap(h.1));
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            assert(x != n);
            pre.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, f));
        assert forall|x: NodeId| #[trigger] b.names.contains_key(x) implies a.names.contains_key(x) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|o: ObjectId| #[trigger] (a.contents)(o) == (b.contents)(o) by {}
        lemma_simulated_discharges_retype(b, a, root, parent, n, live, f);
    }

    /// Nor does anyone's reach change: every capability is as it was, the hidden node is none, and no
    /// node the list held has a new parent, so each state simulates the other.
    pub proof fn lemma_hidden_added_reach(pre: Self, post: Self, parent: usize, n: usize)
        requires
            pre.wf(),
            n < NODE_SPACE,
            !pre.list.nodes@[n as int].live,
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> {
                &&& post.payload_of(x) == pre.payload_of(x)
                &&& post.tables.owner@[page_of(x)] == pre.tables.owner@[page_of(x)]
            },
            post.list.parent@ == pre.list.parent@.insert(n, parent),
        ensures
            forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o),
    {
        let (a, b) = (post.view(), pre.view());
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        let f = |x: NodeId| x;
        assert forall|h: (ObjectId, NodeId)| #[trigger] a.held.contains(h) implies live(h.1) && b.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1) == pre.is_cap(h.1));
            pre.lemma_slot_bound(h.1);
        }
        assert forall|h: (ObjectId, NodeId)| #[trigger] b.held.contains(h) implies live(h.1) && a.held.contains((h.0, f(h.1))) by {
            assert(post.is_cap(h.1) == pre.is_cap(h.1));
            pre.lemma_slot_bound(h.1);
        }
        assert forall|x: NodeId| #[trigger] a.names.contains_key(x) implies {
            &&& live(x)
            &&& b.names.contains_key(f(x))
            &&& b.names[f(x)] == a.names[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| #[trigger] b.names.contains_key(x) implies {
            &&& live(x)
            &&& a.names.contains_key(f(x))
            &&& a.names[f(x)] == b.names[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
            pre.lemma_slot_bound(x);
        }
        assert forall|x: NodeId| #[trigger] a.pages.contains_key(x) implies {
            &&& b.pages.contains_key(f(x))
            &&& b.pages[f(x)] == a.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId| #[trigger] b.pages.contains_key(x) implies {
            &&& a.pages.contains_key(f(x))
            &&& a.pages[f(x)] == b.pages[x]
        } by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] a.rights.contains((x, r)) implies b.rights.contains((f(x), r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId, r: Right| #[trigger] b.rights.contains((x, r)) implies a.rights.contains((f(x), r)) by {
            assert(post.is_cap(x) == pre.is_cap(x));
        }
        assert forall|x: NodeId| live(x) && #[trigger] a.parent.contains_key(x) implies {
            &&& live(a.parent[x])
            &&& b.parent.contains_key(f(x))
            &&& b.parent[f(x)] == f(a.parent[x])
        } by {
            assert(x != n);
            pre.list.lemma_parent_live(x);
        }
        assert forall|x: NodeId| live(x) && #[trigger] b.parent.contains_key(x) implies {
            &&& live(b.parent[x])
            &&& a.parent.contains_key(f(x))
            &&& a.parent[f(x)] == f(b.parent[x])
        } by {
            assert(x != n);
            pre.list.lemma_parent_live(x);
        }
        assert(simulates(a, b, live, f));
        assert(simulates(b, a, live, f));
        assert forall|r: ObjectId, o: ObjectId| #[trigger] a.reach(r, o) == b.reach(r, o) by {
            if a.reach(r, o) {
                lemma_simulates_reach(a, b, live, f, r, o);
            }
            if b.reach(r, o) {
                lemma_simulates_reach(b, a, live, f, r, o);
            }
        }
    }

    /// What a table page's retype does to the fields the view reads: the tables are as they were, and so
    /// is every node the list held.
    pub open spec fn table_page_step(pre: Self, post: Self) -> bool {
        &&& pre.wf()
        &&& post.tables == pre.tables
        &&& forall|x: usize| #[trigger] pre.list.valid(x) ==> {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        }
    }

    /// So the capabilities, and what they say, are as they were.
    pub proof fn lemma_table_page_cap(pre: Self, post: Self, x: usize)
        requires
            Self::table_page_step(pre, post),
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        if pre.tables.owner@.contains_key(page_of(x)) && x % 4096 < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
        }
    }

    proof fn lemma_table_page_caps_wf(pre: Self, post: Self)
        requires
            Self::table_page_step(pre, post),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
            same_frames(&pre.list, &pre.tables, &post.list, &post.tables),
            same_spaces(&pre.list, &pre.tables, &post.list, &post.tables),
            same_threads(&pre.list, &pre.tables, &post.list, &post.tables),
            same_processes(&pre.list, &pre.tables, &post.list, &post.tables),
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            forall|x: usize| #[trigger] pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        assert forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.payload_of(x) == pre.payload_of(x) by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) implies control_named(post.tables.payload_of(x)) by {
            Self::lemma_table_page_cap(pre, post, x);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Space implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Thread implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Thread implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Process implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Process implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n)
            implies cap_wf(post.tables.payload_of(n)) by {
            assert(post.is_cap(n));
            assert(pre.tables.is_cap(&pre.list, n));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Frame implies {
            &&& pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Frame implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_table_page_cap(pre, post, x);
        }
    }

    /// A node the list held before the table page's retype has its kind after, and a leaf's node is one.
    proof fn lemma_table_page_old_node(pre: Self, post: Self, mid: Tree, base: usize, x: usize)
        requires
            Self::table_page_step(pre, post),
            list_grown(pre.list, mid),
            !pre.list.pages@.dom().contains(base),
            x < NODE_SPACE,
            post.list.nodes@[x as int].live,
            x != base ==> post.list.nodes@[x as int].live == mid.nodes@[x as int].live,
        ensures
            x != base ==> pre.list.nodes@[x as int].live && pre.list.valid(x)
                && pre.list.nodes@[x as int].kind == post.list.nodes@[x as int].kind,
    {
        if x != base {
            assert(pre.list.nodes@[x as int].live);
            pre.list.lemma_live_valid(x);
        }
    }

    /// The hidden nodes, the parents, the slots and the leaves after a table page's retype: the new node
    /// is the table page's, hidden under the untyped's capability, and every other node's kind and
    /// parent are as they were.
    proof fn lemma_table_page_nodes(pre: Self, post: Self, mid: Tree, parent: usize, base: usize)
        requires
            Self::table_page_step(pre, post),
            list_grown(pre.list, mid),
            mid.wf(),
            post.list.wf(),
            !pre.list.pages@.dom().contains(base),
            base < NODE_SPACE,
            mid.valid(base),
            !mid.nodes@[base as int].live,
            parent < NODE_SPACE,
            pre.is_cap(parent),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.list.parent@ == mid.parent@.insert(base, parent),
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
            },
            post.table_pages.maps@.contains_key(base),
            forall|t: usize| #[trigger] pre.table_pages.maps@.contains_key(t) ==> post.table_pages.maps@.contains_key(t),
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            Self::lemma_table_page_old_node(pre, post, mid, base, x);
        }
        pre.lemma_slot_bound(parent);
        lemma_parents_same_live(pre.list, mid);
        lemma_parents_derived(mid, post.list, parent, base);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            Self::lemma_table_page_old_node(pre, post, mid, base, x);
            assert(pre.tables.is_cap(&pre.list, x));
            Self::lemma_table_page_cap(pre, post, x);
        }
        assert forall|n: usize| #[trigger] post.list.nodes@[n as int].live && post.tables.owner@.contains_key(page_of(n))
            && n % 4096 != 0 && n % 4096 < NODES_PER_PAGE implies post.list.nodes@[n as int].kind is Capability by {
            pre.lemma_slot_bound(n);
        }
    }

    /// Every node the list held keeps its liveness and kind when pages are added and then node `base`,
    /// dead before, is made.
    proof fn lemma_table_page_kept(pre: Tree, mid: Tree, post: Tree, base: usize)
        requires
            pre.wf(),
            list_grown(pre, mid),
            !pre.valid(base),
            forall|i: int| #![trigger post.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.nodes@[i].live == mid.nodes@[i].live
                &&& post.nodes@[i].kind == mid.nodes@[i].kind
            },
        ensures
            forall|x: usize| #[trigger] pre.valid(x) ==> {
                &&& post.nodes@[x as int].live == pre.nodes@[x as int].live
                &&& post.nodes@[x as int].kind == pre.nodes@[x as int].kind
            },
    {
        assert forall|x: usize| #[trigger] pre.valid(x) implies {
            &&& post.nodes@[x as int].live == pre.nodes@[x as int].live
            &&& post.nodes@[x as int].kind == pre.nodes@[x as int].kind
        } by {
            assert(mid.nodes@[x as int] == pre.nodes@[x as int]);
            pre.lemma_valid_bound(x);
            assert(x != base);
        }
    }

    /// The invariant and the retype's effect once the free order-3 block at `page` is typed as the
    /// table page at `base` under `parent`, from what the body's calls ensure: the block typed, the
    /// node pages added (mid), the hidden node derived, and the page's map, record and spare page
    /// inserted. Its own proof fn so that the body's query stays within budget.
    proof fn lemma_table_page_wf(
        pre: Self,
        mid: Tree,
        post: Self,
        root: usize,
        from: usize,
        parent: usize,
        base: usize,
        page: usize,
        level: usize,
    )
        requires
            pre.wf(),
            pre.tables.roots@.contains_key(root),
            1 <= level <= 3,
            pre.can_retype_under(root, from, base, 3),
            parent == pre.tables.node_of(root, from),
            pre.view().holds_right(root, parent, Right::Retype),
            base % 32768 == 0,
            base + 32768 <= NODE_SPACE,
            page == base / 4096,
            pre.blocks.tracks_run(page as int, 8),
            post.blocks.wf(),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            !pre.blocks.covered(page as int),
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            !post.blocks.pages@[page as int].torn_down,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|k: usize| k < 8 ==> !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                && table_node_page(base, k) % 4096 == 0 && table_node_page(base, k) == base + k * 4096,
            mid.wf(),
            list_grown(pre.list, mid),
            mid.valid(base),
            !mid.nodes@[base as int].live,
            forall|k: usize| k < TABLE_NODE_PAGES ==> mid.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|p: usize| #[trigger] mid.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
            post.list.wf(),
            post.list.is_child(parent, base),
            post.list.parent@ == mid.parent@.insert(base, parent),
            post.list.pages@.dom() == mid.pages@.dom(),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
                &&& post.list.nodes@[i].depth == mid.nodes@[i].depth
            },
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.maps@[base].addr() == base + TABLE_NODE_PAGES * 4096,
            post.table_pages.maps@[base].is_init(),
            post.table_pages.maps@[base].value().wf(),
            post.table_pages.maps@[base].value().level@ == level,
            forall|i: usize| i < 512 ==> #[trigger] post.table_pages.maps@[base].value()[i].is_empty(),
            post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base]),
            post.table_pages.records@[base].addr() == base + TABLE_RECORD_PAGE * 4096,
            post.table_pages.records@[base].is_init(),
            post.table_pages.records@[base].value() == fresh_table(level),
            post.table_pages.spare@ == pre.table_pages.spare@
                .insert((base + 7 * 4096) as usize, post.table_pages.spare@[(base + 7 * 4096) as usize]),
            post.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            post.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
            post.cores == pre.cores,
            post.flush_epoch == pre.flush_epoch,
            post.tlb == pre.tlb,
            post.iommus == pre.iommus,
            post.mapped == pre.mapped,
            post.tables == pre.tables,
            post.stale_epoch == pre.stale_epoch,
            post.frames == pre.frames,
            post.spaces == pre.spaces,
            post.mappings == pre.mappings,
            post.zeroing == pre.zeroing,
            post.holders == pre.holders,
            post.devices == pre.devices,
            post.threads == pre.threads,
            post.processes == pre.processes,
        ensures
            post.wf(),
            forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) ==>
                space_mapping(tree_of(&post.table_pages, &post.spaces), r)
                    == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r),
            forall|x: usize| #[trigger] post.is_cap(x) == pre.is_cap(x),
            discharges(pre.view(), post.view(), root, Effect::Retype { untyped: parent, object: base, into: None }),
            !pre.list.nodes@[base as int].live,
            post.list.parent@ == pre.list.parent@.insert(base, parent),
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base
                ==> post.list.nodes@[i].live == pre.list.nodes@[i].live,
            forall|x: usize| #![trigger post.list.nodes@[x as int]] pre.list.valid(x) && x != base ==> {
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
                &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
            },
            forall|r: ObjectId, o: ObjectId| #[trigger] post.view().reach(r, o) == pre.view().reach(r, o),
    {
        lemma_table_page_base(base, page);
        pre.lemma_slot(root, from);
        pre.lemma_slot_bound(parent);
        assert(pre.blocks.pages@[page as int].kind is Free) by {
            assert(pre.blocks.pages@[page + 0].kind is Free);
        }
        assert(table_node_page(base, 0) == base);
        assert(!pre.list.valid(base));
        assert(!pre.list.nodes@[base as int].live);
        assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
        Self::lemma_table_page_kept(pre.list, mid, post.list, base);
        assert(Self::table_page_step(pre, post));
        Self::lemma_table_page_caps_wf(pre, post);
        Self::lemma_table_page_mappings(pre, post, base, page);
        assert(post.wf()) by {
            pre.tables.lemma_wf_same_pages(&pre.list, &post.list);
            Self::lemma_devices_same_caps(pre, post);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_table_page_nodes(pre, post, mid, parent, base);
            Self::lemma_table_nodes_page_added(pre, post, base);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, base, base);
            Self::lemma_table_page_bindings(pre, post, mid, base);
            Self::lemma_binding_parents_same_caps(pre, post);
            Self::lemma_table_page_blocks(pre, post, base, page);
            Self::lemma_table_page_links(pre, post, base, page);
            Self::lemma_table_page_mapping_parents(pre, post, parent, base);
            Self::lemma_mappings_grown(pre, post, page, 3);
        }
        Self::lemma_hidden_added_discharges(pre, post, root, parent, base);
        Self::lemma_hidden_added_reach(pre, post, parent, base);
        assert forall|x: usize| #![trigger post.list.nodes@[x as int]] pre.list.valid(x) && x != base implies {
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            &&& post.list.nodes@[x as int].depth == pre.list.nodes@[x as int].depth
        } by {
            pre.list.lemma_valid_bound(x);
            assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
        }
    }

    /// A mapping node's parent link is as it was once a node dead before is linked under `parent`.
    proof fn lemma_table_page_mapping_parents(pre: Self, post: Self, parent: usize, base: usize)
        requires
            pre.wf(),
            !pre.list.nodes@[base as int].live,
            post.list.parent@ == pre.list.parent@.insert(base, parent),
        ensures
            forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                ==> post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n],
    {
        assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
            implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
            pre.lemma_mapping_node(n);
        }
    }

    /// The bindings after a table page's retype: its node is hidden, no other node changed, and no
    /// thread or process did.
    proof fn lemma_table_page_bindings(pre: Self, post: Self, mid: Tree, base: usize)
        requires
            pre.wf(),
            list_grown(pre.list, mid),
            base < NODE_SPACE,
            !pre.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != base ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
            },
            post.threads == pre.threads,
            post.processes == pre.processes,
        ensures
            bindings_wf(&post.list, &post.threads, &post.processes),
            same_bindings(&pre.list, &post.list),
    {
        lemma_binding_nodes_grown(pre.list, mid, post.list, base, base);
        lemma_bindings_same(&pre.list, &post.list, &pre.threads, &pre.processes);
    }

    /// The block table's invariants after the free order-3 block at `page` is typed as the table page at
    /// `base`: no leaf, frame or list page lay in it, and the list's new pages are its first five.
    proof fn lemma_table_page_blocks(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::table_page_step(pre, post),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
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
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|k: usize| k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.maps@[base].addr() == base + TABLE_NODE_PAGES * 4096,
            post.table_pages.maps@[base].is_init(),
            post.table_pages.maps@[base].value().wf(),
            post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base]),
            post.table_pages.records@[base].addr() == base + TABLE_RECORD_PAGE * 4096,
            post.table_pages.records@[base].is_init(),
            table_record_wf(&post.table_pages, base),
            post.table_pages.spare@ == pre.table_pages.spare@
                .insert((base + 7 * 4096) as usize, post.table_pages.spare@[(base + 7 * 4096) as usize]),
            post.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            post.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
            post.spaces == pre.spaces,
            post.threads == pre.threads,
            post.processes == pre.processes,
        ensures
            list_pages_used(&post.list, &post.blocks),
            holders_wf(&post.list, &post.tables, &post.blocks, &post.zeroing, post.holders@),
            objects_wf(&post.tables, &post.blocks, post.holders@),
            leaf_blocks_wf(&post.list, &post.tables, &post.blocks),
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
            spaces_wf(&post.list, &post.tables, &post.spaces, &post.blocks),
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
            processes_wf(&post.list, &post.tables, &post.processes, &post.blocks),
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
        assert(!pre.list.pages@.dom().contains(base)) by {
            assert(table_node_page(base, 0) == base);
            assert(pre.blocks.pages@[page + 0int].kind is Free);
        }
        Self::lemma_table_page_caps_wf(pre, post);
        Self::lemma_table_page_list_pages_used(pre, post, base, page);
        assert forall|k: int| 0 <= k < 8 implies !((#[trigger] b.pages@[page + k]).object is Space) by {
            if k == 0 {
                assert(b.pages@[page as int].object is TablePage);
            }
        }
        lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, a, b, page, 8);
        assert forall|k: int| 0 <= k < 8 implies !((#[trigger] b.pages@[page + k]).object is Thread) by {
            if k == 0 {
                assert(b.pages@[page as int].object is TablePage);
            }
        }
        lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, a, b, page, 8);
        assert forall|k: int| 0 <= k < 8 implies !((#[trigger] b.pages@[page + k]).object is Process) by {
            if k == 0 {
                assert(b.pages@[page as int].object is TablePage);
            }
        }
        lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, a, b, page, 8);
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
        }
        lemma_leaf_blocks_same_nodes(&pre.list, &post.list, &pre.tables, b);
        Self::lemma_table_page_pages(pre, post, base, page);
    }

    /// The list's pages after a table page's retype: those it held lie outside the new block, and the
    /// new block's first five are its base and members.
    proof fn lemma_table_page_list_pages_used(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            post.blocks.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            pre.blocks.tracks_run(page as int, 8),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage || post.blocks.pages@[page as int].object is Space,
            post.blocks.pages@[page as int].order == 3,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
        ensures
            list_pages_used(&post.list, &post.blocks),
    {
        let b = &post.blocks;
        lemma_list_pages_used_small_typed(&pre.list, &pre.blocks, b, page, 8);
        assert forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) && b.tracks_addr(p) implies {
            &&& !(b.pages@[(p / 4096) as int].kind is Free)
            &&& b.pages@[(p / 4096) as int].kind is Member
                ==> b.pages@[b.pages@[(p / 4096) as int].base as int].object is TablePage
                    || b.pages@[b.pages@[(p / 4096) as int].base as int].object is Space
            &&& !(b.pages@[(p / 4096) as int].object is Frame)
        } by {
            if !pre.list.pages@.dom().contains(p) {
                let k = choose|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k);
                lemma_table_node_page(base, k);
                assert(p / 4096 == page + k);
                if k != 0 {
                    b.lemma_member_of(page as int, page + k);
                }
            }
        }
    }

    /// The table pages after a table page's retype: the new one has what its block gave, and every other
    /// lay outside the block, keeps its node and keeps its permissions, since no spare page is shared.
    proof fn lemma_table_page_pages(pre: Self, post: Self, base: usize, page: usize)
        requires
            Self::table_page_step(pre, post),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            pre.blocks.tracks_run(page as int, 8),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is TablePage,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|k: usize| k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            !pre.list.pages@.dom().contains(base),
            post.list.nodes@[base as int].live,
            post.list.nodes@[base as int].kind is Hidden,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.maps@[base].addr() == base + TABLE_NODE_PAGES * 4096,
            post.table_pages.maps@[base].is_init(),
            post.table_pages.maps@[base].value().wf(),
            post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base]),
            post.table_pages.records@[base].addr() == base + TABLE_RECORD_PAGE * 4096,
            post.table_pages.records@[base].is_init(),
            table_record_wf(&post.table_pages, base),
            post.table_pages.spare@ == pre.table_pages.spare@
                .insert((base + 7 * 4096) as usize, post.table_pages.spare@[(base + 7 * 4096) as usize]),
            post.table_pages.spare@[(base + 7 * 4096) as usize].addr() == base + 7 * 4096,
            post.table_pages.spare@[(base + 7 * 4096) as usize].is_uninit(),
        ensures
            table_pages_wf(&post.list, &post.table_pages, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let pa = &pre.table_pages;
        let pb = &post.table_pages;
        lemma_table_pages_small_typed(&pre.list, pa, a, b, page, 8);
        assert forall|t: usize| #[trigger] pb.maps@.contains_key(t) implies table_page_wf(&post.list, pb, b, t) by {
            if t == base {
                assert(table_page_wf(&post.list, pb, b, base));
            } else {
                assert(pa.maps@.contains_key(t));
                assert(table_page_wf(&pre.list, pa, b, t));
                pre.lemma_table_page_valid(t);
                assert(t != base);
                assert(pb.maps@[t] == pa.maps@[t]);
                assert(pb.records@[t] == pa.records@[t]);
                assert(pb.spare@[(t + 7 * 4096) as usize] == pa.spare@[(t + 7 * 4096) as usize]);
                assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(t, k)) by {
                    assert(pre.list.pages@.dom().contains(table_node_page(t, k)));
                }
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] table_block(b, x) implies pb.maps@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
            } else if page < x < page + 8 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(pa.maps@.contains_key((x * 4096) as usize));
            }
        }
    }

    /// The kth node page of the block at `page` is free and so not the list's.
    proof fn lemma_table_page_free_list(&self, base: usize, page: usize, k: usize)
        requires
            self.wf(),
            base % 32768 == 0,
            base / 4096 == page,
            self.blocks.tracks_run(page as int, 8),
            k < 8,
            self.blocks.pages@[page + k].kind is Free,
        ensures
            !self.list.pages@.dom().contains(table_node_page(base, k)),
            table_node_page(base, k) % 4096 == 0,
            table_node_page(base, k) == base + k * 4096,
    {
        lemma_table_node_page(base, k);
    }

    /// A free block holds no table and no space.
    pub proof fn lemma_free_not_table(&self, base: usize, page: usize)
        requires
            self.wf(),
            base / 4096 == page,
            self.blocks.pages@[page as int].kind is Free,
        ensures
            !self.table_pages.maps@.contains_key(base),
            !self.spaces.roots@.contains_key(base),
    {
        if self.table_pages.maps@.contains_key(base) {
            assert(table_page_wf(&self.list, &self.table_pages, &self.blocks, base));
        }
        if self.spaces.roots@.contains_key(base) {
            assert(space_wf(&self.list, &self.spaces, &self.blocks, base));
        }
    }

    /// The links after a table page's retype: the new table has no parent, no space and no entry.
    proof fn lemma_table_page_links(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            base / 4096 == page,
            pre.blocks.pages@[page as int].kind is Free,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base]),
            post.table_pages.records@[base].value().parent is None,
            post.table_pages.records@[base].value().space is None,
            forall|i: usize| i < 512 ==> #[trigger] post.table_pages.maps@[base].value()[i].is_empty(),
            post.spaces == pre.spaces,
        ensures
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
    {
        pre.lemma_free_not_table(base, page);
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(b.is_page(base));
        assert forall|i: usize| i < 512 implies #[trigger] b.entry(base, i).is_empty() by {
            assert(post.table_pages.maps@[base].value()[i].is_empty());
        }
        lemma_links_table_added(a, b, base);
    }

    /// The links after a space's retype: the new root has no parent and no entry outside the kernel
    /// slots.
    pub proof fn lemma_space_links(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            base / 4096 == page,
            pre.blocks.pages@[page as int].kind is Free,
            post.table_pages == pre.table_pages,
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            post.spaces.records@[base].value().table.parent is None,
            forall|i: usize| i < 512 && !holds_kernel(post.spaces.records@[base].value().kind, i) ==> #[trigger] post.spaces.roots@[base].value()[i].is_empty(),
        ensures
            table_links_wf(tree_of(&post.table_pages, &post.spaces)),
    {
        pre.lemma_free_not_table(base, page);
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(!b.is_page(base));
        assert(b.is_root(base));
        assert forall|i: usize| i < 512 && !holds_kernel(post.spaces.records@[base].value().kind, i) implies #[trigger] b.entry(base, i).is_empty() by {
            assert(post.spaces.roots@[base].value()[i].is_empty());
        }
        lemma_links_root_added(a, b, base);
    }

    /// A table page's retype leaves every space's mapping as it was: nothing walks to the new table.
    proof fn lemma_table_page_mappings(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            base / 4096 == page,
            pre.blocks.pages@[page as int].kind is Free,
            post.table_pages.maps@ == pre.table_pages.maps@.insert(base, post.table_pages.maps@[base]),
            post.table_pages.records@ == pre.table_pages.records@.insert(base, post.table_pages.records@[base]),
            forall|i: usize| i < 512 ==> #[trigger] post.table_pages.maps@[base].value()[i].is_empty(),
            post.spaces == pre.spaces,
        ensures
            forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) ==>
                space_mapping(tree_of(&post.table_pages, &post.spaces), r)
                    == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
    {
        pre.lemma_free_not_table(base, page);
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) implies {
            &&& b.is_page(t) == a.is_page(t)
            &&& b.is_root(t) == a.is_root(t)
            &&& b.record(t) == a.record(t)
            &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
        } by {
            assert(t != base);
        }
        assert forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) implies
            space_mapping(b, r) == space_mapping(a, r) by {
            lemma_mapping_extended(a, b, r);
        }
        assert forall|u: usize| #[trigger] b.is_page(u) && !a.is_page(u)
            implies forall|i: usize| i < 512 ==> !(#[trigger] b.entry(u, i)).perm.present by {
            assert(u == base);
            assert forall|i: usize| i < 512 implies !(#[trigger] b.entry(u, i)).perm.present by {
                assert(post.table_pages.maps@[base].value()[i].is_empty());
            }
        }
        lemma_frame_entries_extended(a, b);
    }

    /// A space's retype leaves every other's mapping as it was, and the new space maps nothing.
    pub proof fn lemma_space_mappings(pre: Self, post: Self, base: usize, page: usize)
        requires
            pre.wf(),
            base / 4096 == page,
            pre.blocks.pages@[page as int].kind is Free,
            post.table_pages == pre.table_pages,
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            forall|i: usize| i < 512 && !holds_kernel(post.spaces.records@[base].value().kind, i) ==> #[trigger] post.spaces.roots@[base].value()[i].is_empty(),
        ensures
            space_mapping(tree_of(&post.table_pages, &post.spaces), base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty(),
            forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) ==>
                space_mapping(tree_of(&post.table_pages, &post.spaces), r)
                    == space_mapping(tree_of(&pre.table_pages, &pre.spaces), r),
            same_frame_entries(tree_of(&pre.table_pages, &pre.spaces), tree_of(&post.table_pages, &post.spaces)),
    {
        pre.lemma_free_not_table(base, page);
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert(!b.is_page(base));
        assert(b.is_root(base));
        assert forall|i: usize| i < 512 && !holds_kernel(post.spaces.records@[base].value().kind, i) implies #[trigger] b.entry(base, i).is_empty() by {
            assert(post.spaces.roots@[base].value()[i].is_empty());
        }
        lemma_mapping_fresh(b, base);
        assert forall|t: usize| #![trigger a.is_table(t)] a.is_table(t) implies {
            &&& b.is_page(t) == a.is_page(t)
            &&& b.is_root(t) == a.is_root(t)
            &&& b.record(t) == a.record(t)
            &&& forall|i: usize| i < 512 ==> #[trigger] b.entry(t, i) == a.entry(t, i)
        } by {
            assert(t != base);
        }
        assert forall|r: usize| #[trigger] pre.spaces.roots@.contains_key(r) implies
            space_mapping(b, r) == space_mapping(a, r) by {
            lemma_mapping_extended(a, b, r);
        }
        lemma_frame_entries_extended(a, b);
    }

    /// Retypes the free order-3 block at `base` as a table page, under the untyped at index `from` of the
    /// table at `root`. All of these come from user space, and a refusal changes nothing.
    #[verifier::spinoff_prover]
    pub fn retype_table_page(&mut self, root: usize, from: usize, base: usize, level: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            final(self).cores == old(self).cores,
            ret == old(self).can_retype_table_page(root, from, base, level),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[(base / 4096) as int].kind is Free
                &&& final(self).table_pages.maps@.contains_key(base)
                &&& final(self).table_pages.records@[base].value() == fresh_table(level)
                &&& forall|r: usize| #[trigger] old(self).spaces.roots@.contains_key(r) ==>
                    space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                        == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r)
                &&& forall|i: usize| i < 512 ==> #[trigger] final(self).table_pages.maps@[base].value()[i].is_empty()
                &&& final(self).blocks.pages@[(base / 4096) as int].refs == 1
                &&& forall|k: usize| k < TABLE_NODE_PAGES ==> final(self).list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                &&& final(self).list.is_child(parent, base)
                &&& final(self).list.nodes@[base as int].kind is Hidden
                &&& forall|x: usize| #[trigger] final(self).is_cap(x) == old(self).is_cap(x)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None })
                &&& forall|r: ObjectId, o: ObjectId| #[trigger] final(self).view().reach(r, o) == old(self).view().reach(r, o)
                &&& !old(self).list.nodes@[base as int].live
                &&& final(self).list.parent@ == old(self).list.parent@.insert(base, parent)
                &&& forall|i: int| #![trigger final(self).list.nodes@[i]] 0 <= i < NODE_SPACE && i != base
                    ==> final(self).list.nodes@[i].live == old(self).list.nodes@[i].live
                &&& forall|x: usize| #![trigger final(self).list.nodes@[x as int]] old(self).list.valid(x) && x != base ==> {
                    &&& final(self).list.nodes@[x as int].kind == old(self).list.nodes@[x as int].kind
                    &&& final(self).list.nodes@[x as int].depth == old(self).list.nodes@[x as int].depth
                }
                &&& final(self).tables == old(self).tables
                &&& final(self).spaces == old(self).spaces
                &&& final(self).processes == old(self).processes
                &&& final(self).threads == old(self).threads
                &&& final(self).table_pages.maps@ == old(self).table_pages.maps@.insert(base, final(self).table_pages.maps@[base])
                &&& final(self).table_pages.records@ == old(self).table_pages.records@.insert(base, final(self).table_pages.records@[base])
                &&& final(self).blocks.regions_2m@ == old(self).blocks.regions_2m@
                &&& final(self).blocks.regions_1g@ == old(self).blocks.regions_1g@
                &&& forall|i: int| old(self).blocks.tracks(i) && !(base / 4096 <= i < base / 4096 + 8)
                    ==> #[trigger] final(self).blocks.pages@[i] == old(self).blocks.pages@[i]
            },
    {
        let ghost pre = *old(self);
        if level == 0 || level > 3 {
            return false;
        }
        let parent = match self.retype_parent(root, from, base, 3) {
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
        let Tracked(perms) = match self.blocks.try_type(page, 3, ObjectType::TablePage) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let ghost all = perms;
        let tracked first;
        let tracked second;
        let tracked third;
        let tracked fourth;
        let tracked fifth;
        let tracked table;
        let tracked sixth;
        let tracked seventh;
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
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
            third = perms.tracked_remove((page + 2) as usize);
            fourth = perms.tracked_remove((page + 3) as usize);
            fifth = perms.tracked_remove((page + 4) as usize);
            table = perms.tracked_remove((page + 5) as usize);
            sixth = perms.tracked_remove((page + 6) as usize);
            seventh = perms.tracked_remove((page + 7) as usize);
            assert forall|k: usize| k < 8 implies !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                && table_node_page(base, k) % 4096 == 0 && table_node_page(base, k) == base + k * 4096 by {
                assert(pre.blocks.pages@[page + k].kind is Free);
                pre.lemma_table_page_free_list(base, page, k);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot_bound(parent);
        }
        add_node_pages(&mut self.list, base, Tracked(first), Tracked(second), Tracked(third), Tracked(fourth), Tracked(fifth));
        let ghost mid = self.list;
        proof {
            mid.lemma_seq_fits();
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
        }
        self.list.derive(parent, base, NodeKind::Hidden);
        let (_, Tracked(map)) = page_perm_to_page_map(base + TABLE_NODE_PAGES * 4096, Ghost(level), Tracked(table));
        let tracked mut record;
        proof {
            record = page_into_table_record(sixth);
        }
        PPtr::<TableRecord>::from_usize(base + TABLE_RECORD_PAGE * 4096).put(
            Tracked(&mut record),
            TableRecord { level, space: None, parent: None, written: false },
        );
        proof {
            self.table_pages.maps.borrow_mut().tracked_insert(base, map);
            self.table_pages.records.borrow_mut().tracked_insert(base, record);
            self.table_pages.spare.borrow_mut().tracked_insert((base + 7 * 4096) as usize, seventh);
        }
        proof {
            Self::lemma_table_page_wf(pre, mid, *self, root, from, parent, base, page, level);
            Self::lemma_bound_threads_same(pre, *self);
        }
        true
    }

    /// What a space's retype does to the fields the view reads: one slot becomes a capability, and
    /// every other node the list held, and every other slot, is as it was.
    pub open spec fn space_step(pre: Self, post: Self, child: usize) -> bool {
        &&& pre.wf()
        &&& post.tables.owner == pre.tables.owner
        &&& forall|x: usize| #[trigger] pre.list.valid(x) && x != child ==> {
            &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
            &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
        }
        &&& forall|x: usize| #![trigger post.tables.payload_of(x)]
            x != child && x % 4096 < NODES_PER_PAGE && pre.tables.owner@.contains_key(page_of(x))
            ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
    }

    /// So any other node is a capability after exactly when it was before, saying the same.
    pub proof fn lemma_space_cap_frame(pre: Self, post: Self, child: usize, x: usize)
        requires
            Self::space_step(pre, post, child),
            x != child,
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        if pre.tables.owner@.contains_key(page_of(x)) && x % 4096 < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
        }
    }

    /// Every capability still names a block, and the step adds the one capability.
    pub proof fn lemma_space_caps_wf(pre: Self, post: Self, child: usize)
        requires
            Self::space_step(pre, post, child),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            cap_wf(post.payload_of(child)),
            control_named(post.payload_of(child)),
        ensures
            post.tables.caps_wf(&post.list),
            post.tables.control_wf(&post.list),
            Self::adds_cap(pre, post, child),
            forall|x: usize| x != child ==> {
                &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
                &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
            },
    {
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert forall|x: usize| #![trigger post.is_cap(x)] #![trigger pre.is_cap(x)]
            x != child implies post.is_cap(x) == pre.is_cap(x) by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) implies {
            &&& cap_wf(post.tables.payload_of(n))
            &&& control_named(post.tables.payload_of(n))
        } by {
            if n != child {
                assert(pre.tables.is_cap(&pre.list, n));
            }
        }
    }

    /// The hidden nodes, the parents, the slots and the leaves after a space's retype: the one new
    /// live node is the capability in its slot, below a capability or the list's first node, and
    /// every other node's kind and parent are as they were.
    pub proof fn lemma_space_nodes(pre: Self, post: Self, mid: Tree, parent: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            list_grown(pre.list, mid),
            mid.wf(),
            post.list.wf(),
            parent < NODE_SPACE,
            pre.is_cap(parent) || parent == pre.list.seq@[0],
            child < NODE_SPACE,
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.list.parent@ == mid.parent@.insert(child, parent),
            post.list.seq@[0] == mid.seq@[0],
            forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != child ==> {
                &&& post.list.nodes@[i].live == mid.nodes@[i].live
                &&& post.list.nodes@[i].kind == mid.nodes@[i].kind
            },
            post.table_pages == pre.table_pages,
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            parents_are_capabilities(&post.list),
            capability_nodes_are_slots(&post.list, &post.tables),
            first_node_outside_leaves(&post.list, &post.tables),
            leaf_slots_are_capabilities(&post.list, &post.tables),
            forall|x: usize| x < NODE_SPACE && x != child && (#[trigger] post.list.nodes@[x as int]).live
                ==> pre.list.nodes@[x as int].live && pre.list.valid(x),
    {
        assert forall|x: usize| x < NODE_SPACE && x != child && (#[trigger] post.list.nodes@[x as int]).live implies {
            &&& pre.list.nodes@[x as int].live
            &&& pre.list.valid(x)
            &&& pre.list.nodes@[x as int].kind == post.list.nodes@[x as int].kind
        } by {
            assert(mid.nodes@[x as int].live == pre.list.nodes@[x as int].live);
            pre.list.lemma_live_valid(x);
        }
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != child);
        }
        if pre.is_cap(parent) {
            pre.lemma_slot_bound(parent);
        } else {
            pre.list.lemma_link(0);
            pre.list.lemma_live_valid(parent);
        }
        lemma_parents_same_live(pre.list, mid);
        lemma_parents_derived(mid, post.list, parent, child);
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Capability && x != post.list.seq@[0]
            implies post.tables.is_cap(&post.list, x) by {
            if x != child {
                assert(pre.tables.is_cap(&pre.list, x));
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
        }
        assert(post.list.seq@[0] == pre.list.seq@[0]);
        assert forall|n: usize| #[trigger] post.list.nodes@[n as int].live && post.tables.owner@.contains_key(page_of(n))
            && n % 4096 != 0 && n % 4096 < NODES_PER_PAGE implies post.list.nodes@[n as int].kind is Capability by {
            if n != child {
                pre.lemma_slot_bound(n);
            }
        }
    }

    /// The space clause after a space's retype at base: the new space's node pages were not the list's,
    /// and the one node that came alive is the capability in a leaf's slot, outside every space.
    proof fn lemma_space_nodes_added(pre: Self, post: Self, base: usize, child: usize)
        requires
            pre.wf(),
            base % 32768 == 0,
            pre.blocks.tracks_addr_run(base, 8),
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            forall|k: usize| k < 8 ==> !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            pre.list.valid(child),
            pre.tables.owner@.contains_key(page_of(child)),
            forall|x: usize| x < NODE_SPACE && x != child && (#[trigger] post.list.nodes@[x as int]).live
                ==> pre.list.nodes@[x as int].live && pre.list.valid(x),
        ensures
            space_nodes_dead(&post.list, &post.spaces),
    {
        assert forall|s: usize, k: usize, i: usize| #![trigger table_node(s, k, i)]
            post.spaces.roots@.contains_key(s) && post.spaces.records@[s].value().kind is Device && k < TABLE_NODE_PAGES
                && i < NODES_PER_PAGE
            implies !post.list.nodes@[table_node(s, k, i) as int].live by {
            let x = table_node(s, k, i);
            if s == base {
                lemma_table_node_place(base, k, i);
                assert(!pre.list.pages@.dom().contains(table_node_page(base, k)));
                assert(!pre.list.valid(x));
            } else {
                assert(pre.spaces.roots@.contains_key(s));
                pre.lemma_space_node_in_block(s, k, i);
                assert(x != child);
            }
        }
    }

    /// The spaces after a space's retype: the new one has what its block gave and holds its one
    /// capability, and every other lay outside the block, keeps its pages and keeps its holders.
    proof fn lemma_spaces_space_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % 32768 == 0,
            base / 4096 == page,
            page * 4096 == base,
            pre.blocks.tracks_run(page as int, 8),
            forall|k: int| 0 <= k < 8 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| pre.blocks.tracks(i) && !(page <= i < page + 8) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Space,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|k: usize| k < TABLE_NODE_PAGES ==> post.list.pages@.dom().contains(#[trigger] table_node_page(base, k)),
            post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]),
            post.spaces.roots@[base].addr() == base + SPACE_ROOT_PAGE * 4096,
            post.spaces.roots@[base].is_init(),
            post.spaces.roots@[base].value().wf(),
            post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]),
            post.spaces.records@[base].addr() == base + SPACE_RECORD_PAGE * 4096,
            post.spaces.records@[base].is_init(),
            post.spaces.records@[base].value().root == base + SPACE_ROOT_PAGE * 4096,
            post.spaces.records@[base].value().kind is Device,
            post.spaces.loaded@ == pre.spaces.loaded@.insert(base, post.spaces.loaded@[base]),
            post.spaces.loaded@[base].addr() == base + SPACE_CORES_PAGE * 4096,
            post.spaces.loaded@[base].is_init(),
            post.spaces.loaded@[base].value().list == 0u32,
            post.spaces.kernel_entries == pre.spaces.kernel_entries,
            kernel_slots_wf(&post.spaces, base),
            root_record_wf(&post.spaces, base),
            post.spaces.holders@ == pre.spaces.holders@.insert(base, set![child]),
            post.spaces.bound@ == pre.spaces.bound@.insert(base, Set::<usize>::empty()),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == space_of(base),
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
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|s: usize| #[trigger] sb.roots@.contains_key(s) implies space_wf(&post.list, sb, b, s) by {
            if s == base {
                assert(sb.holders@[base] == set![child]);
                assert(sb.holders@[base].finite());
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
                if sa.records@[s].value().kind is Device {
                    assert forall|k: usize| k < TABLE_NODE_PAGES implies post.list.pages@.dom().contains(#[trigger] table_node_page(s, k)) by {
                        assert(pre.list.pages@.dom().contains(table_node_page(s, k)));
                    }
                }
            }
        }
        assert forall|x: usize| b.tracks(x as int) && #[trigger] space_block(b, x) implies sb.roots@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
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
            if n == child {
                assert(sb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let t = pre.tables.payload_of(n).base;
                assert(sa.roots@.contains_key(t));
                assert(t != base);
                assert(sb.holders@[t] == sa.holders@[t]);
            }
        }
        assert forall|s: usize, n: usize| sb.roots@.contains_key(s) && #[trigger] sb.holders@[s].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Space
            &&& post.tables.payload_of(n).base == s
        } by {
            if s == base {
                assert(n == child);
            } else {
                assert(sa.roots@.contains_key(s));
                assert(sa.holders@[s].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The block table's invariants after the free order-3 block at `page` is typed as the space at
    /// `base`: no leaf, frame or list page lay in it, the list's new pages are its first five, and no
    /// holder changed.
    proof fn lemma_space_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
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
            post.blocks.pages@[page as int].object is Space,
            post.blocks.pages@[page as int].order == 3,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 8 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            forall|p: usize| #[trigger] post.list.pages@.dom().contains(p) ==> pre.list.pages@.dom().contains(p)
                || exists|k: usize| k < TABLE_NODE_PAGES && p == #[trigger] table_node_page(base, k),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child).kind is Space,
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
        Self::lemma_table_page_list_pages_used(pre, post, base, page);
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
                assert(b.pages@[page as int].object is Space);
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

    /// Retypes the free block at `base` as a device space, under the untyped at index `from` of the table at
    /// `root`, with its capability at the empty index `to`. All of these come from user space, and a
    /// refusal changes nothing. A process's space is part of its process: see retype_process.
    pub fn retype_space(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
            old(self).root_live(root),
        ensures
            final(self).wf(),
            bound_threads(&final(self).list, &final(self).tables) == bound_threads(&old(self).list, &old(self).tables),
            ret == old(self).can_retype_block(root, from, to, base, 3),
            !ret ==> *final(self) == *old(self),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[(base / 4096) as int].kind is Free
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == space_of(base)
                &&& final(self).list.is_child(parent, child)
                &&& final(self).spaces.roots@.contains_key(base)
                &&& final(self).spaces.records@[base].value().kind is Device
                &&& final(self).spaces.records@[base].value().table == fresh_root(base)
                &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] final(self).loaded(c, base)
                &&& forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] holds_id(final(self).cores@, final(self).spaces.loaded@, c, base)
                &&& space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), base) == IMap::<SpacePath, crate::pagetable::entry::PageEntry>::empty()
                &&& forall|r: usize| #[trigger] old(self).spaces.roots@.contains_key(r) ==>
                    space_mapping(tree_of(&final(self).table_pages, &final(self).spaces), r)
                        == space_mapping(tree_of(&old(self).table_pages, &old(self).spaces), r)
                &&& forall|i: usize| i < 512 ==> #[trigger] final(self).spaces.roots@[base].value()[i].is_empty()
                &&& final(self).spaces.kernel_entries == old(self).spaces.kernel_entries
                &&& final(self).spaces.bound@ == old(self).spaces.bound@.insert(base, Set::<usize>::empty())
                &&& forall|s: usize| #[trigger] old(self).spaces.roots@.contains_key(s) ==> final(self).spaces.roots@[s] == old(self).spaces.roots@[s]
                &&& final(self).blocks.pages@[(base / 4096) as int].refs == 1
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base, into: None })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, 3) {
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
        let Tracked(perms) = match self.blocks.try_type(page, 3, ObjectType::Space) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let ghost all = perms;
        let tracked first;
        let tracked second;
        let tracked third;
        let tracked fourth;
        let tracked fifth;
        let tracked table;
        let tracked record;
        let tracked spare;
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
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
            third = perms.tracked_remove((page + 2) as usize);
            fourth = perms.tracked_remove((page + 3) as usize);
            fifth = perms.tracked_remove((page + 4) as usize);
            table = perms.tracked_remove((page + 5) as usize);
            record = perms.tracked_remove((page + 6) as usize);
            spare = perms.tracked_remove((page + 7) as usize);
            assert forall|k: usize| k < 8 implies !pre.list.pages@.dom().contains(#[trigger] table_node_page(base, k))
                && table_node_page(base, k) % 4096 == 0 && table_node_page(base, k) == base + k * 4096 by {
                assert(pre.blocks.pages@[page + k].kind is Free);
                pre.lemma_table_page_free_list(base, page, k);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
        }
        add_node_pages(&mut self.list, base, Tracked(first), Tracked(second), Tracked(third), Tracked(fourth), Tracked(fifth));
        let ghost mid = self.list;
        proof {
            mid.lemma_seq_fits();
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
            assert(mid.nodes@[child as int] == pre.list.nodes@[child as int]);
        }
        let root_table = base + SPACE_ROOT_PAGE * 4096;
        let (_, Tracked(map)) = page_perm_to_page_map(root_table, Ghost(4), Tracked(table));
        let tracked map = map;
        let tracked mut typed;
        let tracked mut cores;
        proof {
            typed = page_into_space_record(record);
            cores = page_into_core_list(spare);
        }
        let ids = vstd::array::array_fill_for_copy_types::<usize, NUM_CPUS>(0usize);
        PPtr::<SpaceCores>::from_usize(base + SPACE_CORES_PAGE * 4096).put(Tracked(&mut cores), SpaceCores { list: 0u32, ids });
        let pptr = PPtr::<SpaceRecord>::from_usize(base + SPACE_RECORD_PAGE * 4096);
        pptr.put(
            Tracked(&mut typed),
            SpaceRecord { kind: SpaceKind::Device, root: root_table, table: TableRecord { level: 4, space: Some(base), parent: None, written: false } },
        );
        proof {
            self.spaces.roots.borrow_mut().tracked_insert(base, map);
            self.spaces.records.borrow_mut().tracked_insert(base, typed);
            self.spaces.loaded.borrow_mut().tracked_insert(base, cores);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Space, order: 3, rights: SPACE_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.spaces.holders = Ghost(pre.spaces.holders@.insert(base, set![child]));
        self.spaces.bound = Ghost(pre.spaces.bound@.insert(base, Set::<usize>::empty()));
        proof {
            let post = *self;
            assert forall|x: usize| #[trigger] pre.list.valid(x) && x != child implies {
                &&& post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live
                &&& post.list.nodes@[x as int].kind == pre.list.nodes@[x as int].kind
            } by {
                assert(mid.nodes@[x as int] == pre.list.nodes@[x as int]);
                pre.list.lemma_valid_bound(x);
            }
            assert(Self::space_step(pre, post, child));
            assert(post.payload_of(child) == space_of(base));
            assert(2u32 & 128u32 == 0) by (bit_vector);
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
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            assert(post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]));
            Self::lemma_space_nodes_added(pre, post, base, child);
            assert(post.list.pages@.dom() == mid.pages@.dom());
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            lemma_binding_nodes_grown(pre.list, mid, post.list, child, child);
            lemma_bindings_kept(&pre.list, &post.list, &pre.threads, &post.threads, &pre.processes, &post.processes);
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_binding_parents_same_caps(pre, post);
            Self::lemma_space_blocks(pre, post, base, page, child);
            assert(post.spaces.roots@ == pre.spaces.roots@.insert(base, post.spaces.roots@[base]));
            assert(post.spaces.records@ == pre.spaces.records@.insert(base, post.spaces.records@[base]));
            assert(post.spaces.loaded@ == pre.spaces.loaded@.insert(base, post.spaces.loaded@[base]));
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
            assert forall|k: int| 0 < k < 8 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
                post.blocks.lemma_member_of(page as int, page + k);
            }
            Self::lemma_spaces_space_added(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 8 implies !((#[trigger] post.blocks.pages@[page + k]).object is Thread) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Space);
                }
            }
            lemma_threads_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.threads, &pre.blocks, &post.blocks, page, 8);
            assert forall|k: int| 0 <= k < 8 implies !((#[trigger] post.blocks.pages@[page + k]).object is Process) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Space);
                }
            }
            lemma_processes_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.processes, &pre.blocks, &post.blocks, page, 8);
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
            }
            Self::lemma_devices_same_caps(pre, post);
            assert(post.wf());
            Self::lemma_bound_threads_same(pre, post);
            assert(SPACE_RIGHTS & 128 == 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            Self::lemma_places_child_view(pre, post, root, from, root, to);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_child_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
        }
        true
    }
}

} // verus!
