// SPDX-License-Identifier: MIT

//! The kernel as reach sees it. Every capability operation's spec states discharges over this view,
//! so what a process holds, what each capability names and which rights it carries are read from the
//! tables here and nowhere else, beside what each device space maps, read from the walks of its tables,
//! and which space each device is bound to, read from the device records, and what a process sees of
//! a frame, read from its page's permission, and of a thread, read from the registers its record saves.
//! The fields for process mappings and threads, and the contents of objects other than frames and
//! threads, stay empty until the objects behind them exist. See design/theorem-over-reach/ and design/device-binding-under-the-space-capability/.
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::arch::*;
#[cfg(verus_keep_ghost)]
use crate::capability::device::*;
use crate::capability::kernel::*;
#[cfg(verus_keep_ghost)]
use crate::capability::link::*;
#[cfg(verus_keep_ghost)]
use crate::capability::list::*;
#[cfg(verus_keep_ghost)]
use crate::capability::mapping::*;
#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::space::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::capability::thread::*;
#[cfg(verus_keep_ghost)]
use crate::define::*;
#[cfg(verus_keep_ghost)]
use crate::pagetable::entry::PageEntry;
#[cfg(verus_keep_ghost)]
use crate::pptr::*;

/// The bit of a capability's rights word that grants this right.
pub open spec fn right_bit(right: Right) -> u32 {
    match right {
        Right::Read => 1,
        Right::Write => 2,
        Right::Execute => 4,
        Right::Retype => 8,
        Right::Send => 16,
        Right::Receive => 32,
        Right::Grant => 64,
        Right::Control => 128,
    }
}

/// Each thread bound to a process, read from its binding node: a live binding node's parent is a
/// capability to the process the thread is bound to. Read from the list and the tables alone, as
/// view_of is. See design/process-holds-capabilities/.
pub open spec fn bound_threads(list: &Tree, tables: &Tables) -> Map<ObjectId, ObjectId> {
    Map::new(
        Set::range(0usize, NODE_SPACE).filter(|t: usize| list.nodes@[t as int].live && list.nodes@[t as int].kind is Binding),
        |t: usize| tables.payload_of(list.parent@[t]).base,
    )
}

/// The nodes live in list, as bound_threads reads them.
pub open spec fn live_nodes(list: &Tree) -> Set<usize> {
    Set::range(0usize, NODE_SPACE).filter(|t: usize| list.nodes@[t as int].live)
}

/// The process thread t's record names, if t has a record and it names one.
pub open spec fn thread_process(threads: &Threads, t: usize) -> Option<ObjectId> {
    if threads.records@.contains_key(t) { threads.records@[t].value().process } else { None }
}

/// The process each thread's record names.
pub open spec fn record_processes(threads: &Threads) -> Map<ObjectId, ObjectId> {
    Map::new(
        threads.records@.dom().filter(|t: usize| thread_process(threads, t) is Some),
        |t: usize| thread_process(threads, t)->Some_0,
    )
}

/// t is in the record-named map exactly when its record names a process, and maps to that process.
pub proof fn lemma_record_processes(threads: &Threads, t: usize)
    ensures
        record_processes(threads).dom().contains(t) == thread_process(threads, t) is Some,
        thread_process(threads, t) is Some ==> record_processes(threads)[t] == thread_process(threads, t)->Some_0,
{
    broadcast use vstd::set::lemma_set_filter;
}

/// The bound threads are those whose binding node is live.
pub proof fn lemma_bound_threads_live(list: &Tree, tables: &Tables)
    ensures
        bound_threads(list, tables) == bound_threads(list, tables).restrict(live_nodes(list)),
{
    broadcast use vstd::set::lemma_set_filter;
    assert(bound_threads(list, tables) =~= bound_threads(list, tables).restrict(live_nodes(list)));
}

/// Space s is a space of its own, a device space or a nested table, rather than a process's: whoever
/// holds a capability to it sees what it maps.
pub open spec fn is_device(tree: TableTree, s: usize) -> bool {
    &&& tree.is_root(s)
    &&& !(tree.space_records[s].value().kind is Process)
}

/// Device space s maps page o: a walk of s's tables finds it.
pub open spec fn shares_page(tree: TableTree, s: ObjectId, o: ObjectId) -> bool {
    &&& is_device(tree, s)
    &&& o % PAGE_SZ == 0
    &&& exists|p: SpacePath| #[trigger] walk_finds(tree, s, p, (o / PAGE_SZ) as usize)
}

/// Each device space with each page it maps: whoever sees the space reaches the page.
/// See design/device-binding-under-the-space-capability/.
pub open spec fn shares_of(tree: TableTree) -> ISet<(ObjectId, ObjectId)> {
    ISet::new(|x: (ObjectId, ObjectId)| shares_page(tree, x.0, x.1))
}

/// Space s with each page a map of first page `frame`, large or not, maps: what such a map into device
/// space s adds to the shares.
pub open spec fn map_shares(s: ObjectId, frame: usize, large: bool) -> ISet<(ObjectId, ObjectId)> {
    ISet::new(|x: (ObjectId, ObjectId)| {
        &&& x.0 == s
        &&& x.1 % PAGE_SZ == 0
        &&& frame <= x.1 / PAGE_SZ < frame + entry_pages(map_level(large))
    })
}

/// b's device spaces map nothing a's did not: each walk of a device space of b that finds a frame is a
/// walk of a device space of a that finds the same.
pub open spec fn shares_kept(a: TableTree, b: TableTree) -> bool {
    forall|s: usize, p: SpacePath| is_device(b, s) && #[trigger] walk(b, s, p) is Some
        ==> is_device(a, s) && walk(b, s, p) == walk(a, s, p)
}

/// So b shares nothing a did not.
pub proof fn lemma_shares_kept(a: TableTree, b: TableTree)
    requires
        shares_kept(a, b),
    ensures
        shares_of(b).subset_of(shares_of(a)),
{
    assert forall|x: (ObjectId, ObjectId)| #[trigger] shares_of(b).contains(x) implies shares_of(a).contains(x) by {
        let p = choose|p: SpacePath| #[trigger] walk_finds(b, x.0, p, (x.1 / PAGE_SZ) as usize);
        assert(walk(b, x.0, p) is Some);
        assert(is_device(a, x.0));
        assert(walk(b, x.0, p) == walk(a, x.0, p));
        assert(walk_finds(a, x.0, p, (x.1 / PAGE_SZ) as usize));
    }
}

/// Trees that keep each other's shares share the same.
pub proof fn lemma_shares_same(a: TableTree, b: TableTree)
    requires
        shares_kept(a, b),
        shares_kept(b, a),
    ensures
        shares_of(b) == shares_of(a),
{
    lemma_shares_kept(a, b);
    lemma_shares_kept(b, a);
    assert(shares_of(b) =~= shares_of(a));
}

/// Trees whose walks find the same, a space of both being a device space of both or of neither, share
/// the same: a space of one alone has no walk in the other, so none in either.
pub proof fn lemma_same_walks_same_shares(a: TableTree, b: TableTree)
    requires
        forall|s: usize, p: SpacePath| #[trigger] walk(b, s, p) == walk(a, s, p),
        forall|s: usize| #![trigger is_device(b, s)] #![trigger is_device(a, s)]
            a.is_root(s) && b.is_root(s) ==> is_device(b, s) == is_device(a, s),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|s: usize, p: SpacePath| is_device(b, s) && #[trigger] walk(b, s, p) is Some
        implies is_device(a, s) && walk(b, s, p) == walk(a, s, p) by {
        assert(walk(b, s, p) == walk(a, s, p));
        assert(a.is_root(s));
    }
    assert forall|s: usize, p: SpacePath| is_device(a, s) && #[trigger] walk(a, s, p) is Some
        implies is_device(b, s) && walk(a, s, p) == walk(b, s, p) by {
        assert(walk(b, s, p) == walk(a, s, p));
        assert(b.is_root(s));
    }
    lemma_shares_same(a, b);
}

/// So do trees with the same device spaces, each mapping the same.
pub proof fn lemma_same_mapping_same_shares(a: TableTree, b: TableTree)
    requires
        forall|s: usize| #![trigger is_device(b, s)] #![trigger is_device(a, s)] is_device(b, s) == is_device(a, s),
        forall|s: usize| #[trigger] is_device(a, s) ==> space_mapping(b, s) == space_mapping(a, s),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|s: usize, p: SpacePath| is_device(b, s) && #[trigger] walk(b, s, p) is Some
        implies is_device(a, s) && walk(b, s, p) == walk(a, s, p) by {
        assert(is_device(a, s));
        assert(space_mapping(b, s).contains_key(p) == space_mapping(a, s).contains_key(p));
        assert(space_mapping(b, s)[p] == space_mapping(a, s)[p]);
    }
    assert forall|s: usize, p: SpacePath| is_device(a, s) && #[trigger] walk(a, s, p) is Some
        implies is_device(b, s) && walk(a, s, p) == walk(b, s, p) by {
        assert(is_device(b, s));
        assert(space_mapping(b, s).contains_key(p) == space_mapping(a, s).contains_key(p));
        assert(space_mapping(b, s)[p] == space_mapping(a, s)[p]);
    }
    lemma_shares_same(a, b);
}

/// A tree with one more space, which maps nothing, shares the same when every other device space maps
/// what it did.
pub proof fn lemma_space_added_same_shares(a: TableTree, b: TableTree, base: usize)
    requires
        !a.is_root(base),
        forall|s: usize| #![trigger is_device(b, s)] #![trigger is_device(a, s)] s != base ==> is_device(b, s) == is_device(a, s),
        forall|s: usize| #[trigger] is_device(a, s) ==> space_mapping(b, s) == space_mapping(a, s),
        space_mapping(b, base) == IMap::<SpacePath, PageEntry>::empty(),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|s: usize, p: SpacePath| is_device(b, s) && #[trigger] walk(b, s, p) is Some
        implies is_device(a, s) && walk(b, s, p) == walk(a, s, p) by {
        if s == base {
            assert(space_mapping(b, base).contains_key(p));
            assert(!IMap::<SpacePath, PageEntry>::empty().contains_key(p));
        } else {
            assert(is_device(a, s));
            assert(space_mapping(b, s).contains_key(p) == space_mapping(a, s).contains_key(p));
            assert(space_mapping(b, s)[p] == space_mapping(a, s)[p]);
        }
    }
    assert forall|s: usize, p: SpacePath| is_device(a, s) && #[trigger] walk(a, s, p) is Some
        implies is_device(b, s) && walk(a, s, p) == walk(b, s, p) by {
        assert(s != base);
        assert(is_device(b, s));
        assert(space_mapping(b, s).contains_key(p) == space_mapping(a, s).contains_key(p));
        assert(space_mapping(b, s)[p] == space_mapping(a, s)[p]);
    }
    lemma_shares_same(a, b);
}

/// A tree without a table page that has no parent and no entry shares the same: no walk reached it.
pub proof fn lemma_table_removed_same_shares(a: TableTree, b: TableTree, t: usize)
    requires
        table_removed(a, b, t),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|s: usize, p: SpacePath| #[trigger] walk(b, s, p) == walk(a, s, p) by {
        lemma_walk_table_removed(a, b, t, s, p);
    }
    lemma_same_walks_same_shares(a, b);
}

/// A tree without a space whose root names no child shares the same: the space mapped nothing.
pub proof fn lemma_space_removed_same_shares(a: TableTree, b: TableTree, s: usize)
    requires
        space_removed(a, b, s),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|r: usize, p: SpacePath| #[trigger] walk(b, r, p) == walk(a, r, p) by {
        lemma_walk_space_removed(a, b, s, r, p);
    }
    assert forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)]
        a.is_root(r) && b.is_root(r) implies is_device(b, r) == is_device(a, r) by {
        assert(r != s);
    }
    lemma_same_walks_same_shares(a, b);
}

/// What a's device spaces share through the walks `gone` does not name: each device space with each page
/// such a walk of it finds. A step that ends exactly the walks `gone` names leaves these shared, so a
/// page another walk of the space still finds stays.
pub open spec fn shares_surviving(a: TableTree, gone: spec_fn(usize, SpacePath) -> bool) -> ISet<(ObjectId, ObjectId)> {
    ISet::new(|x: (ObjectId, ObjectId)| {
        &&& is_device(a, x.0)
        &&& x.1 % PAGE_SZ == 0
        &&& exists|p: SpacePath| !gone(x.0, p) && #[trigger] walk_finds(a, x.0, p, (x.1 / PAGE_SZ) as usize)
    })
}

/// A tree whose walks are a's but for those `gone` names, which find nothing, with a's device spaces,
/// shares what a shares through the walks that remain.
pub proof fn lemma_walks_ended_shares(a: TableTree, b: TableTree, gone: spec_fn(usize, SpacePath) -> bool)
    requires
        forall|s: usize, p: SpacePath| #[trigger] walk(b, s, p) == if gone(s, p) { None } else { walk(a, s, p) },
        forall|s: usize| #![trigger is_device(b, s)] #![trigger is_device(a, s)]
            a.is_root(s) && b.is_root(s) ==> is_device(b, s) == is_device(a, s),
    ensures
        shares_of(b) == shares_surviving(a, gone),
{
    assert forall|x: (ObjectId, ObjectId)| #[trigger] shares_of(b).contains(x)
        implies shares_surviving(a, gone).contains(x) by {
        let g = (x.1 / PAGE_SZ) as usize;
        let p = choose|p: SpacePath| #[trigger] walk_finds(b, x.0, p, g);
        assert(walk(b, x.0, p) == if gone(x.0, p) { None } else { walk(a, x.0, p) });
        assert(!gone(x.0, p) && walk_finds(a, x.0, p, g));
    }
    assert forall|x: (ObjectId, ObjectId)| #[trigger] shares_surviving(a, gone).contains(x)
        implies shares_of(b).contains(x) by {
        let g = (x.1 / PAGE_SZ) as usize;
        let p = choose|p: SpacePath| !gone(x.0, p) && #[trigger] walk_finds(a, x.0, p, g);
        assert(walk(b, x.0, p) == walk(a, x.0, p));
        assert(walk_finds(b, x.0, p, g));
    }
    assert(shares_of(b) =~= shares_surviving(a, gone));
}

/// What a map into space s adds to the shares: pages of the frame its entry v names, under s, and only
/// when s is a device space.
pub proof fn lemma_mapped_shares(a: TableTree, b: TableTree, s: usize, p: SpacePath, v: PageEntry, x: (ObjectId, ObjectId))
    requires
        forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r),
        space_mapping(b, s) == space_mapping(a, s).insert(p, v),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
        shares_of(b).contains(x),
        !shares_of(a).contains(x),
    ensures
        x.0 == s,
        is_device(a, s),
        x.1 % PAGE_SZ == 0,
        v.addr / PAGE_SZ <= x.1 / PAGE_SZ < v.addr / PAGE_SZ + entry_pages(if v.perm.ps { 2usize } else { 1usize }),
{
    let g = (x.1 / PAGE_SZ) as usize;
    let q = choose|q: SpacePath| #[trigger] walk_finds(b, x.0, q, g);
    assert(is_device(a, x.0));
    assert(space_mapping(b, x.0).contains_key(q));
    if x.0 != s || q != p {
        assert(space_mapping(a, x.0).contains_key(q));
        assert(space_mapping(b, x.0)[q] == space_mapping(a, x.0)[q]);
        assert(walk_finds(a, x.0, q, g));
        assert(shares_page(a, x.0, x.1));
    }
    assert(space_mapping(b, s)[p] == v);
}

/// A map of entry v at a path p that device space s did not map adds to the shares s with each page v
/// maps, and nothing else.
pub proof fn lemma_mapped_device_shares(a: TableTree, b: TableTree, s: usize, p: SpacePath, v: PageEntry)
    requires
        forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r),
        is_device(a, s),
        walk(a, s, p) is None,
        space_mapping(b, s) == space_mapping(a, s).insert(p, v),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
    ensures
        shares_of(b) == shares_of(a).union(map_shares(s, (v.addr / PAGE_SZ) as usize, v.perm.ps)),
{
    let added = map_shares(s, (v.addr / PAGE_SZ) as usize, v.perm.ps);
    assert forall|x: (ObjectId, ObjectId)| #[trigger] shares_of(b).contains(x)
        implies shares_of(a).union(added).contains(x) by {
        if !shares_of(a).contains(x) {
            lemma_mapped_shares(a, b, s, p, v, x);
        }
    }
    assert forall|x: (ObjectId, ObjectId)| #[trigger] shares_of(a).contains(x) implies shares_of(b).contains(x) by {
        let g = (x.1 / PAGE_SZ) as usize;
        let q = choose|q: SpacePath| #[trigger] walk_finds(a, x.0, q, g);
        assert(space_mapping(a, x.0).contains_key(q));
        assert(space_mapping(b, x.0).contains_key(q));
        assert(space_mapping(b, x.0)[q] == space_mapping(a, x.0)[q]);
        assert(walk_finds(b, x.0, q, g));
    }
    assert forall|x: (ObjectId, ObjectId)| #[trigger] added.contains(x) implies shares_of(b).contains(x) by {
        let g = (x.1 / PAGE_SZ) as usize;
        assert(space_mapping(b, s).contains_key(p));
        assert(space_mapping(b, s)[p] == v);
        assert(walk_finds(b, s, p, g));
    }
    assert(shares_of(b) =~= shares_of(a).union(added));
}

/// A map into a space that is no device space shares the same.
pub proof fn lemma_mapped_same_shares(a: TableTree, b: TableTree, s: usize)
    requires
        forall|r: usize| #![trigger is_device(b, r)] #![trigger is_device(a, r)] is_device(b, r) == is_device(a, r),
        !is_device(a, s),
        forall|r: usize| r != s ==> #[trigger] space_mapping(b, r) == space_mapping(a, r),
    ensures
        shares_of(b) == shares_of(a),
{
    assert forall|r: usize| #[trigger] is_device(a, r) implies space_mapping(b, r) == space_mapping(a, r) by {
        assert(r != s);
    }
    lemma_same_mapping_same_shares(a, b);
}

/// Every space is a process space, as while boot builds the root, which makes no other.
pub open spec fn no_device_space(spaces: &Spaces) -> bool {
    forall|s: usize| #[trigger] spaces.roots@.contains_key(s) ==> spaces.records@[s].value().kind is Process
}

/// Each bound device with the device space its record names: the holder of the device sees the space.
/// See design/device-binding-under-the-space-capability/.
pub open spec fn binds_of(devices: &Devices) -> IMap<ObjectId, ObjectId> {
    IMap::new(
        |o: ObjectId| devices.names(o) && devices.records@[device_of(o)].space is Some,
        |o: ObjectId| devices.records@[device_of(o)].space->Some_0,
    )
}

/// What a process sees of page o: its bytes, when the kernel holds the page as a frame and it is
/// written, and nothing otherwise. Contents are per page, so a block's pages change one by one.
pub open spec fn frame_contents(frames: Map<usize, PagePerm4k>, o: ObjectId) -> Seq<u8> {
    let i = (o / PAGE_SZ) as usize;
    if o % PAGE_SZ == 0 && frames.contains_key(i) && frames[i].is_init() {
        frames[i].value()@
    } else {
        Seq::empty()
    }
}

/// Words as bytes, each word's least significant byte first.
pub open spec fn words_bytes(words: Seq<u64>) -> Seq<u8> {
    Seq::new(words.len() * 8, |i: int| ((words[i / 8] >> ((8 * (i % 8)) as u64)) & 0xff) as u8)
}

/// The registers each thread's record saves, keyed by the thread.
pub open spec fn saved_registers(threads: &Threads) -> Map<ObjectId, Registers> {
    threads.records@.map_values(|r: PointsTo<ThreadRecord>| r.value().frame)
}

/// What a process sees of object o: a thread's saved registers, as bytes, and a frame's page otherwise.
pub open spec fn contents_of(registers: Map<ObjectId, Registers>, frames: Map<usize, PagePerm4k>, o: ObjectId) -> Seq<u8> {
    if registers.contains_key(o) {
        words_bytes(register_words(registers[o]))
    } else {
        frame_contents(frames, o)
    }
}

/// Two frame maps that agree on every page outside the `pages` pages from first differ in contents
/// only on those pages.
pub proof fn lemma_contents_in_pages(a: Map<usize, PagePerm4k>, b: Map<usize, PagePerm4k>, first: usize, pages: nat, o: ObjectId)
    requires
        first % PAGE_SZ == 0,
        forall|i: usize| !(first / PAGE_SZ <= i < first / PAGE_SZ + pages)
            ==> (#[trigger] a.contains_key(i) == b.contains_key(i) && (a.contains_key(i) ==> a[i] == b[i])),
        frame_contents(a, o) != frame_contents(b, o),
    ensures
        in_pages(first, pages, o),
{
    let i = (o / PAGE_SZ) as usize;
    assert(o % PAGE_SZ == 0);
    if !(first / PAGE_SZ <= i < first / PAGE_SZ + pages) {
        assert(a.contains_key(i) == b.contains_key(i));
        assert(false);
    }
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(first as int, PAGE_SZ as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o as int, PAGE_SZ as int);
}

/// What the view reads: the list and the tables, what the device spaces map through the table tree,
/// which space each device is bound to, the threads' saved registers and the frames' pages, so a step
/// that leaves those alone leaves the view alone.
pub open spec fn view_of(
    list: &Tree,
    tables: &Tables,
    tree: TableTree,
    devices: &Devices,
    registers: Map<ObjectId, Registers>,
    frames: Map<usize, PagePerm4k>,
) -> State {
    State {
        held: ISet::new(|h: (ObjectId, NodeId)|
            tables.is_cap(list, h.1) && tables.owner@[page_of(h.1)].0 == h.0),
        names: IMap::new(|n: NodeId| tables.is_cap(list, n), |n: NodeId| tables.payload_of(n).base),
        pages: IMap::new(|n: NodeId| tables.is_cap(list, n), |n: NodeId| pow2(tables.payload_of(n).order as nat)),
        rights: ISet::new(|h: (NodeId, Right)|
            tables.is_cap(list, h.0) && tables.payload_of(h.0).rights & right_bit(h.1) != 0),
        parent: list.parent@,
        maps: Set::empty(),
        process_of: Map::empty(),
        waiting: Set::empty(),
        bound: Map::empty(),
        shares: shares_of(tree),
        binds: binds_of(devices),
        contents: |o: ObjectId| contents_of(registers, frames, o),
    }
}

impl CapKernel {
    pub open spec fn is_cap(&self, n: usize) -> bool {
        self.tables.is_cap(&self.list, n)
    }

    pub open spec fn payload_of(&self, n: usize) -> Payload {
        self.tables.payload_of(n)
    }

    /// A step that takes walks away and puts none in, with no new device space, shares no more.
    pub proof fn lemma_shrunk_sheds(pre: Self, post: Self)
        requires
            Self::mappings_shrunk(pre, post),
            forall|s: usize| #[trigger] is_device(tree_of(&post.table_pages, &post.spaces), s)
                && tree_of(&pre.table_pages, &pre.spaces).is_root(s) ==> is_device(tree_of(&pre.table_pages, &pre.spaces), s),
        ensures
            post.view().shares.subset_of(pre.view().shares),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        assert forall|s: usize, p: SpacePath| is_device(b, s) && #[trigger] walk(b, s, p) is Some
            implies is_device(a, s) && walk(b, s, p) == walk(a, s, p) by {
            assert(walk(b, s, p) == walk(a, s, p));
            assert(a.is_root(s));
        }
        lemma_shares_kept(a, b);
    }

    /// Unlinking the mapping of entry e of table t ends the walks that ended there, so the device spaces
    /// share what the other walks find.
    pub proof fn lemma_unlinked_shares(pre: Self, post: Self, n: usize, t: usize, e: usize)
        requires
            Self::mapping_unlinked(pre, post, n),
            pre.mappings@[n].table == t,
            pre.mappings@[n].entry == e,
            post.spaces == pre.spaces,
        ensures
            post.view().shares == shares_surviving(
                tree_of(&pre.table_pages, &pre.spaces),
                |r: usize, q: SpacePath| ends_at(tree_of(&pre.table_pages, &pre.spaces), r, q, t, e),
            ),
    {
        let a = tree_of(&pre.table_pages, &pre.spaces);
        let b = tree_of(&post.table_pages, &post.spaces);
        let gone = |r: usize, q: SpacePath| ends_at(a, r, q, t, e);
        reveal(walks_cut);
        assert forall|s: usize, q: SpacePath| #[trigger] walk(b, s, q) == if gone(s, q) { None } else { walk(a, s, q) } by {
            assert(walk(b, s, q) == if ends_at(a, s, q, t, e) { None } else { walk(a, s, q) });
        }
        lemma_walks_ended_shares(a, b, gone);
    }

    pub open spec fn view(&self) -> State {
        view_of(&self.list, &self.tables, tree_of(&self.table_pages, &self.spaces), &self.devices, saved_registers(&self.threads), self.frames@)
    }

    /// Without a device space nothing is shared through one.
    pub proof fn lemma_no_device_no_shares(&self)
        requires
            no_device_space(&self.spaces),
        ensures
            forall|x: (ObjectId, ObjectId)| !#[trigger] self.view().shares.contains(x),
    {
        assert forall|x: (ObjectId, ObjectId)| !#[trigger] self.view().shares.contains(x) by {
            if self.view().shares.contains(x) {
                assert(self.spaces.roots@.contains_key(x.0));
            }
        }
    }

    /// Nor is any device bound, since a bound device's space is a device space.
    pub proof fn lemma_no_device_no_binds(&self)
        requires
            self.wf(),
            no_device_space(&self.spaces),
        ensures
            forall|o: ObjectId| !#[trigger] self.view().binds.contains_key(o),
    {
        assert forall|o: ObjectId| !#[trigger] self.view().binds.contains_key(o) by {
            if self.view().binds.contains_key(o) {
                self.lemma_binds(o);
                self.lemma_bound_device(device_of(o));
                assert(self.spaces.roots@.contains_key(self.devices.records@[device_of(o)].space->Some_0));
            }
        }
    }

    /// Where a node in a leaf's page lies.
    pub proof fn lemma_slot_bound(&self, n: usize)
        requires
            self.wf(),
            self.tables.owner@.contains_key(page_of(n)),
            n % PAGE_SZ < NODES_PER_PAGE,
        ensures
            n < NODE_SPACE,
            self.list.valid(n),
    {
        self.tables.lemma_leaf(&self.list, page_of(n));
        self.list.lemma_valid_bound(n);
    }

    /// Where the node of a slot lies, and whose it is.
    pub proof fn lemma_slot(&self, root: usize, i: usize)
        requires
            self.wf(),
            self.tables.has_slot(&self.list, root, i),
        ensures
            self.tables.owner@.contains_key(page_of(self.tables.node_of(root, i))),
            self.tables.owner@[page_of(self.tables.node_of(root, i))].0 == root,
            self.tables.node_of(root, i) % PAGE_SZ == index_slot(i),
            0 < index_slot(i) < NODES_PER_PAGE,
            page_of(self.tables.node_of(root, i)) == self.tables.leaf(root, index_entry(i)),
    {
        let leaf = self.tables.leaf(root, index_entry(i));
        self.tables.lemma_entry(root, index_entry(i));
        self.tables.lemma_leaf(&self.list, leaf);
        let n = self.tables.node_of(root, i);
        assert(leaf % PAGE_SZ == 0);
        assert(n % PAGE_SZ == index_slot(i));
        assert(page_of(n) == leaf);
    }

    /// Index i of the table at root is a slot, of node n, and n is a capability saying p.
    pub open spec fn slot_holds(&self, root: usize, i: usize, n: usize, p: Payload) -> bool {
        &&& self.tables.has_slot(&self.list, root, i)
        &&& self.tables.node_of(root, i) == n
        &&& self.is_cap(n)
        &&& self.payload_of(n) == p
    }

    /// A slot stays a slot of the same node while the tables' roots stay and no live node dies.
    pub proof fn lemma_slot_stays(pre: Self, post: Self, root: usize, i: usize)
        requires
            pre.wf(),
            pre.tables.has_slot(&pre.list, root, i),
            post.tables.roots == pre.tables.roots,
            forall|j: int| 0 <= j < NODE_SPACE && #[trigger] pre.list.nodes@[j].live ==> post.list.nodes@[j].live,
        ensures
            post.tables.has_slot(&post.list, root, i),
            post.tables.node_of(root, i) == pre.tables.node_of(root, i),
    {
        pre.lemma_slot(root, i);
        let n = pre.tables.node_of(root, i);
        pre.lemma_slot_bound(n);
        let leaf = pre.tables.leaf(root, index_entry(i));
        assert(leaf == page_of(n));
        assert(leaf <= n);
        assert(pre.list.nodes@[leaf as int].live);
    }

    /// Between pre and post, no node but n and m changed its liveness or kind, and no capability but
    /// those what it says.
    pub open spec fn caps_frame(pre: Self, post: Self, n: usize, m: usize) -> bool {
        &&& pre.wf()
        &&& post.tables.owner == pre.tables.owner
        &&& forall|i: int| #![trigger post.list.nodes@[i]] 0 <= i < NODE_SPACE && i != n && i != m ==> {
            &&& post.list.nodes@[i].live == pre.list.nodes@[i].live
            &&& post.list.nodes@[i].kind == pre.list.nodes@[i].kind
        }
        &&& forall|x: usize| #![trigger post.tables.payload_of(x)]
            x != n && x != m && x % PAGE_SZ < NODES_PER_PAGE && pre.tables.owner@.contains_key(page_of(x))
            ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
    }

    /// So any other node is a capability after exactly when it was before, saying the same.
    pub proof fn lemma_caps_frame(pre: Self, post: Self, n: usize, m: usize, x: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            x != n,
            x != m,
        ensures
            post.is_cap(x) == pre.is_cap(x),
            pre.is_cap(x) ==> post.payload_of(x) == pre.payload_of(x),
    {
        if pre.tables.owner@.contains_key(page_of(x)) && x % PAGE_SZ < NODES_PER_PAGE {
            pre.lemma_slot_bound(x);
            assert(post.list.nodes@[x as int].live == pre.list.nodes@[x as int].live);
            assert(post.tables.payload_of(x) == pre.tables.payload_of(x));
        }
    }

    /// The step changed no node's kind or liveness but n's and m's. They are slots, so neither is a
    /// leaf's first node, and neither is now a live hidden node, so the hidden nodes are as they were.
    pub proof fn lemma_hidden_frame(pre: Self, post: Self, n: usize, m: usize)
        requires
            Self::caps_frame(pre, post, n, m),
            post.table_pages == pre.table_pages,
            n % PAGE_SZ != 0,
            m % PAGE_SZ != 0,
            !(post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Hidden),
            !(post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Hidden),
            post.list.nodes@[n as int].live && post.list.nodes@[n as int].kind is Capability
                && n != post.list.seq@[0] ==> post.is_cap(n),
            post.list.nodes@[m as int].live && post.list.nodes@[m as int].kind is Capability
                && m != post.list.seq@[0] ==> post.is_cap(m),
            post.list.seq@[0] == pre.list.seq@[0] || pre.list.seq@[0] == n || pre.list.seq@[0] == m,
        ensures
            hidden_nodes_are_leaves(&post.list, &post.tables, &post.table_pages),
            capability_nodes_are_slots(&post.list, &post.tables),
    {
        assert forall|x: usize| x < NODE_SPACE && (#[trigger] post.list.nodes@[x as int]).live
            && post.list.nodes@[x as int].kind is Hidden
            implies post.tables.owner@.contains_key(x) || post.table_pages.maps@.contains_key(x) by {
            assert(x != n && x != m);
            assert(pre.list.nodes@[x as int].live);
        }
    }

    /// An ancestor by the list is an ancestor by the view: each link is a parent the map holds.
    pub proof fn lemma_anc_descends(&self, r: usize, n: nat)
        requires
            self.list.wf(),
            has(self.list.seq@, r),
            n <= self.list.d(r),
        ensures
            self.view().descends(self.list.anc(r, n), r, n),
        decreases n,
    {
        if n > 0 {
            let s = self.list.seq@;
            lemma_has(s, r);
            let k = choose|k: int| 0 <= k < s.len() && s[k] == r;
            assert(k != 0);
            assert(self.list.parent@.contains_key(s[k]));
            assert(has(s, self.list.parent@[s[k]]));
            assert(self.list.d(r) == self.list.d(self.list.parent@[r]) + 1);
            self.lemma_anc_descends(self.list.parent@[r], (n - 1) as nat);
        }
    }

    /// A capability that names a block names one within the address space, so it covers no device, not
    /// the console and not power: each is reached only through its own capability.
    pub proof fn lemma_covers_no_device(&self, n: usize, o: ObjectId)
        requires
            self.wf(),
            self.is_cap(n),
            names_block(self.payload_of(n).kind),
            self.view().covers(n, o),
        ensures
            o < DEVICE_OBJECTS,
    {
    }

    /// The console's capability covers the console's page alone and a power capability power's page
    /// alone, each past memory and every device object, and no other capability covers either page.
    pub proof fn lemma_covers_console_or_power(&self, n: usize, o: ObjectId)
        requires
            self.wf(),
            self.is_cap(n),
            self.view().covers(n, o),
        ensures
            self.payload_of(n).kind is Console ==> o == CONSOLE_OBJECT,
            self.payload_of(n).kind is Power ==> o == POWER_OBJECT,
            self.payload_of(n).kind is Console || self.payload_of(n).kind is Power ==> DEVICE_OBJECTS <= o,
            self.payload_of(n).kind is Console || self.payload_of(n).kind is Power
                ==> forall|d: int| 0 <= d < MAX_DEVICES ==> o != #[trigger] device_object(d),
            !(self.payload_of(n).kind is Console) ==> o != CONSOLE_OBJECT,
            !(self.payload_of(n).kind is Power) ==> o != POWER_OBJECT,
    {
        let p = self.payload_of(n);
        if p.kind is Device {
            reveal(devices_wf);
            assert(devices_wf(&self.list, &self.tables, &self.devices));
            assert(self.devices.count <= MAX_DEVICES);
            let x = (p.base - DEVICE_OBJECTS) as int;
            assert(x / (PAGE_SZ as int) < MAX_DEVICES);
            assert(x < MAX_DEVICES * PAGE_SZ) by (nonlinear_arith)
                requires x / (PAGE_SZ as int) < MAX_DEVICES, x >= 0;
            assert(pow2(0) == 1) by { lemma2_to64(); }
        } else if p.kind is Console || p.kind is Power {
            assert(pow2(0) == 1) by { lemma2_to64(); }
        }
    }

    /// Only the holder of device d's capability reaches the device directly: a capability naming a block,
    /// the console or power covers no device object, the one capability naming d does, and its only
    /// ancestor is the list's first node, which no process holds. So binding d to a space feeds the reach
    /// of its holder alone. See design/device-binding-under-the-space-capability/.
    pub proof fn lemma_direct_device_held(&self, q: ObjectId, d: int)
        requires
            self.wf(),
            0 <= d < self.devices.count,
            self.view().direct(q, device_object(d)),
        ensures
            self.devices.holder@.contains_key(device_object(d)),
            self.view().holds(q, self.devices.holder@[device_object(d)]),
    {
        let o = device_object(d);
        let v = self.view();
        reveal(devices_wf);
        assert(self.devices.count <= MAX_DEVICES);
        lemma_device_object(d);
        let (c, x, k) = choose|c: NodeId, x: NodeId, k: nat| #[trigger] v.descends(c, x, k) && v.holds(q, c) && v.covers(x, o);
        assert(self.is_cap(x));
        self.lemma_covers_console_or_power(x, o);
        let p = self.payload_of(x);
        if names_block(p.kind) {
            self.lemma_covers_no_device(x, o);
        }
        assert(p.kind is Device);
        assert(pow2(0) == 1) by { lemma2_to64(); }
        let e = device_of(p.base);
        lemma_device_object(e);
        assert(p.base == device_object(e));
        assert(e == d) by (nonlinear_arith)
            requires
                DEVICE_OBJECTS + e * PAGE_SZ <= DEVICE_OBJECTS + d * PAGE_SZ < DEVICE_OBJECTS + e * PAGE_SZ + PAGE_SZ,
                PAGE_SZ > 0,
        ;
        assert(self.devices.holder@[o] == x);
        if k > 0 {
            let first = self.list.seq@[0];
            assert(self.list.parent@[x] == first);
            assert(v.descends(c, first, (k - 1) as nat));
            assert(!self.list.parent@.contains_key(first));
            assert(c == first);
            assert(first_node_outside_leaves(&self.list, &self.tables));
            assert(!self.is_cap(first));
        }
    }

    /// The view's binds are what the binding nodes say: a device is bound exactly when its record names a
    /// space, and then its binding node is live under a capability to that space. See
    /// design/device-binding-under-the-space-capability/.
    pub proof fn lemma_binds(&self, o: ObjectId)
        requires
            self.wf(),
        ensures
            self.view().binds.contains_key(o) == (self.devices.names(o) && self.devices.records@[device_of(o)].space is Some),
            self.view().binds.contains_key(o) ==> {
                let d = device_of(o);
                let x = binding_node(&self.devices, d);
                &&& o == device_object(d)
                &&& 0 <= d < self.devices.count
                &&& self.view().binds[o] == self.devices.records@[d].space->Some_0
                &&& x < NODE_SPACE
                &&& self.list.nodes@[x as int].live
                &&& self.list.nodes@[x as int].kind is DeviceBinding
                &&& device_binding_parent(&self.list, &self.tables, x, self.view().binds[o])
            },
    {
        reveal(devices_wf);
        reveal(device_bindings_wf);
        if self.view().binds.contains_key(o) {
            let d = device_of(o);
            assert((o - DEVICE_OBJECTS) % (PAGE_SZ as int) == 0);
            assert(o == device_object(d));
            assert(self.devices.records@[d].space is Some);
        }
    }

    /// The binding nodes name what the thread records name: bindings_wf makes a live binding node
    /// exactly a bound thread, and binding_parents makes its parent a capability to that process.
    pub proof fn lemma_bound_threads(&self)
        requires
            self.wf(),
        ensures
            bound_threads(&self.list, &self.tables) == record_processes(&self.threads),
    {
        broadcast use vstd::set::lemma_set_filter;
        let b = bound_threads(&self.list, &self.tables);
        let r = record_processes(&self.threads);
        assert forall|t: usize| #[trigger] b.dom().contains(t) == r.dom().contains(t) by {
            lemma_record_processes(&self.threads, t);
            if t < NODE_SPACE && self.list.nodes@[t as int].live && self.list.nodes@[t as int].kind is Binding {
                self.lemma_binding_parent(t);
            }
            if self.threads.records@.contains_key(t) && self.threads.records@[t].value().process is Some {
                assert(t < NODE_SPACE && self.list.nodes@[t as int].live);
            }
        }
        assert forall|t: usize| #[trigger] b.dom().contains(t) implies b[t] == r[t] by {
            lemma_record_processes(&self.threads, t);
            self.lemma_binding_parent(t);
        }
        assert(b =~= r);
    }

    /// Two states whose thread records name the same process for every thread have the same bound
    /// threads.
    pub proof fn lemma_bound_threads_same(pre: Self, post: Self)
        requires
            pre.wf(),
            post.wf(),
            forall|t: usize| #[trigger] thread_process(&post.threads, t) == thread_process(&pre.threads, t),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == record_processes(&pre.threads).dom().contains(x)
            && (record_processes(&post.threads).dom().contains(x)
                ==> record_processes(&post.threads)[x] == record_processes(&pre.threads)[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= record_processes(&pre.threads));
    }

    /// A step whose thread records gain exactly t bound to p gains exactly t -> p.
    pub proof fn lemma_bound_threads_insert(pre: Self, post: Self, t: usize, p: ObjectId)
        requires
            pre.wf(),
            post.wf(),
            thread_process(&post.threads, t) == Some(p),
            forall|x: usize| x != t ==> #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).insert(t, p),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        let a = record_processes(&pre.threads).insert(t, p);
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == a.dom().contains(x)
            && (a.dom().contains(x) ==> record_processes(&post.threads)[x] == a[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= a);
    }

    /// A step whose thread records lose exactly t's process loses exactly t.
    pub proof fn lemma_bound_threads_remove(pre: Self, post: Self, t: usize)
        requires
            pre.wf(),
            post.wf(),
            thread_process(&post.threads, t) is None,
            forall|x: usize| x != t ==> #[trigger] thread_process(&post.threads, x) == thread_process(&pre.threads, x),
        ensures
            bound_threads(&post.list, &post.tables) == bound_threads(&pre.list, &pre.tables).remove(t),
    {
        pre.lemma_bound_threads();
        post.lemma_bound_threads();
        let a = record_processes(&pre.threads).remove(t);
        assert forall|x: usize|
            #[trigger] record_processes(&post.threads).dom().contains(x) == a.dom().contains(x)
            && (a.dom().contains(x) ==> record_processes(&post.threads)[x] == a[x]) by {
            lemma_record_processes(&pre.threads, x);
            lemma_record_processes(&post.threads, x);
        }
        assert(record_processes(&post.threads) =~= a);
    }

    /// A step that changes nothing discharges the lemma.
    pub proof fn lemma_no_op_discharges(&self, p: ObjectId)
        ensures
            discharges(self.view(), self.view(), p, Effect::Local),
    {
    }
}

} // verus!
