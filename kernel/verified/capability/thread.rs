//! Threads as retyped objects. A thread is an order-1 block: a node page, whose nodes are its bindings
//! to its process, its fault endpoint and its placement, then a page holding its record at the start
//! and its extended register state, the XSAVE area, after it. A capability names a thread by its
//! block's base and carries control, and the capabilities naming it hold its block's references. See
//! design/process-holds-capabilities/.
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

use crate::capability::block::*;
use crate::capability::derive::*;
use crate::capability::device::*;
use crate::capability::kernel::*;
use crate::capability::list::*;
use crate::capability::mapping::*;
use crate::capability::reach::*;
use crate::capability::refs::*;
use crate::capability::space::*;
use crate::capability::table::*;
use crate::capability::view::*;
use crate::define::*;
use crate::layouts::*;
use crate::pptr::*;
use crate::trap::Registers;

/// A thread's block is two pages.
pub const THREAD_ORDER: u8 = 1;

/// The page of a thread's block that holds its record and its XSAVE area. Page 0 is its node page.
pub const THREAD_RECORD_PAGE: usize = 1;

/// Where the XSAVE area starts in the record's page: past the record, and 64-byte aligned as XSAVE
/// requires.
pub const XSAVE_OFFSET: usize = 1024;

/// The bytes the XSAVE area has, to the end of the page. CPUID leaf 0xD, sub-leaf 0, reports 2440 for
/// every state component the reference host supports.
pub const XSAVE_BYTES: usize = 3072;

/// A thread capability carries control: it may start, stop and configure the thread.
pub const THREAD_RIGHTS: u32 = 128;

/// What a thread is doing.
#[derive(Clone, Copy)]
pub enum ThreadState {
    Inactive,
}

/// What a thread keeps at the start of its record's page. Its XSAVE area lies after it in the same
/// page, inside the record's permission.
#[derive(Clone, Copy)]
pub struct ThreadRecord {
    pub state: ThreadState,
    /// The registers saved when it last left user mode.
    pub frame: Registers,
    /// Set when it must stop on its core's next kernel entry.
    pub pending_stop: bool,
}

/// Registers that are all zero.
pub open spec fn zero_registers() -> Registers {
    Registers {
        r15: 0,
        r14: 0,
        r13: 0,
        r12: 0,
        rbp: 0,
        rbx: 0,
        r11: 0,
        r10: 0,
        r9: 0,
        r8: 0,
        rcx: 0,
        rdx: 0,
        rsi: 0,
        rdi: 0,
        rax: 0,
        error_code: 0,
        rip: 0,
        cs: 0,
        flags: 0,
        rsp: 0,
        ss: 0,
    }
}

/// A thread's record when it is typed: inactive, with zeroed registers and no stop pending.
pub open spec fn fresh_thread() -> ThreadRecord {
    ThreadRecord { state: ThreadState::Inactive, frame: zero_registers(), pending_stop: false }
}

fn new_thread_record() -> (ret: ThreadRecord)
    ensures
        ret == fresh_thread(),
{
    ThreadRecord {
        state: ThreadState::Inactive,
        frame: Registers {
            r15: 0,
            r14: 0,
            r13: 0,
            r12: 0,
            rbp: 0,
            rbx: 0,
            r11: 0,
            r10: 0,
            r9: 0,
            r8: 0,
            rcx: 0,
            rdx: 0,
            rsi: 0,
            rdi: 0,
            rax: 0,
            error_code: 0,
            rip: 0,
            cs: 0,
            flags: 0,
            rsp: 0,
            ss: 0,
        },
        pending_stop: false,
    }
}

/// A thread capability's payload.
pub open spec fn thread_of(base: usize) -> Payload {
    Payload { kind: CapKind::Thread, order: THREAD_ORDER, rights: THREAD_RIGHTS, base, badge: 0, reserved: 0 }
}

/// Each thread's record by its block's address, and the capabilities holding its block.
pub struct Threads {
    pub records: Tracked<Map<usize, PointsTo<ThreadRecord>>>,
    pub holders: Ghost<IMap<usize, Set<usize>>>,
}

impl Threads {
    pub fn new() -> (ret: Self)
        ensures
            ret.records@ == Map::<usize, PointsTo<ThreadRecord>>::empty(),
            ret.holders@ == IMap::<usize, Set<usize>>::empty(),
    {
        Threads { records: Tracked(Map::tracked_empty()), holders: Ghost(IMap::empty()) }
    }
}

/// The block at page b holds a thread.
pub open spec fn thread_block(blocks: &BlockTable, b: usize) -> bool {
    &&& blocks.pages@[b as int].kind is Base
    &&& blocks.pages@[b as int].object is Thread
}

/// The thread at t has its record and its node page. Its block's references are exactly its holders,
/// and it is dead at once when they go.
pub open spec fn thread_wf(list: &Tree, threads: &Threads, blocks: &BlockTable, t: usize) -> bool {
    &&& t % 8192 == 0
    &&& t / 4096 + 2 <= NUM_PAGES
    &&& threads.records@[t].addr() == t + THREAD_RECORD_PAGE * 4096
    &&& threads.records@[t].is_init()
    &&& blocks.pages@[(t / 4096) as int].kind is Base
    &&& blocks.pages@[(t / 4096) as int].object is Thread
    &&& blocks.pages@[(t / 4096) as int].order == 1
    &&& list.pages@.dom().contains(t)
    &&& threads.holders@.contains_key(t)
    &&& threads.holders@[t].finite()
    &&& threads.holders@[t].len() == blocks.pages@[(t / 4096) as int].refs
    &&& blocks.pages@[(t / 4096) as int].refs == 0 ==> blocks.pages@[(t / 4096) as int].dead
}

/// Each thread is well formed, a thread's block is one of these, and the capabilities of kind Thread
/// are exactly the holders.
pub open spec fn threads_wf(list: &Tree, tables: &Tables, threads: &Threads, blocks: &BlockTable) -> bool {
    &&& forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> thread_wf(list, threads, blocks, t)
    &&& forall|b: usize| b < NUM_PAGES && #[trigger] thread_block(blocks, b)
        ==> threads.records@.contains_key((b * 4096) as usize)
    &&& forall|n: usize| #[trigger] tables.is_cap(list, n) && tables.payload_of(n).kind is Thread ==> {
        &&& threads.records@.contains_key(tables.payload_of(n).base)
        &&& threads.holders@[tables.payload_of(n).base].contains(n)
        &&& tables.payload_of(n).order == THREAD_ORDER
    }
    &&& forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) ==> {
        &&& tables.is_cap(list, n)
        &&& tables.payload_of(n).kind is Thread
        &&& tables.payload_of(n).base == t
    }
}

/// Each thread's holders after node i is renamed n.
pub open spec fn moved_thread_holders(holders: IMap<usize, Set<usize>>, i: usize, n: usize) -> IMap<usize, Set<usize>> {
    IMap::new(
        |t: usize| holders.contains_key(t),
        |t: usize| if holders[t].contains(i) { holders[t].remove(i).insert(n) } else { holders[t] },
    )
}

/// The thread capabilities of a and b are the same, saying the same.
pub open spec fn same_threads(list_a: &Tree, tables_a: &Tables, list_b: &Tree, tables_b: &Tables) -> bool {
    &&& forall|x: usize| #[trigger] tables_b.is_cap(list_b, x) && tables_b.payload_of(x).kind is Thread ==> {
        &&& tables_a.is_cap(list_a, x)
        &&& tables_a.payload_of(x) == tables_b.payload_of(x)
    }
    &&& forall|x: usize| #[trigger] tables_a.is_cap(list_a, x) && tables_a.payload_of(x).kind is Thread ==> {
        &&& tables_b.is_cap(list_b, x)
        &&& tables_b.payload_of(x) == tables_a.payload_of(x)
    }
}

/// The threads read nothing of the list but its pages, and nothing of the capabilities but the
/// threads'.
pub proof fn lemma_threads_same_caps(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    blocks: &BlockTable,
)
    requires
        threads_wf(list_a, tables_a, threads, blocks),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, blocks),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, blocks, t) by {
        assert(thread_wf(list_a, threads, blocks, t));
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Thread implies {
        &&& threads.records@.contains_key(tables_b.payload_of(n).base)
        &&& threads.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == THREAD_ORDER
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Thread
        &&& tables_b.payload_of(n).base == t
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// And nothing of the block table but its page entries.
pub proof fn lemma_threads_same_pages(list: &Tree, tables: &Tables, threads: &Threads, a: &BlockTable, b: &BlockTable)
    requires
        threads_wf(list, tables, threads, a),
        b.pages@ == a.pages@,
    ensures
        threads_wf(list, tables, threads, b),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list, threads, b, t) by {
        assert(thread_wf(list, threads, a, t));
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        assert(thread_block(a, x));
    }
}

/// A step that changes the count of a block that is no thread's leaves every thread's block as it was.
pub proof fn lemma_threads_refs_changed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    br: BlockRef,
    refs: usize,
    dead: bool,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        blocks_refs_changed(a, b, br, refs, dead),
        match br {
            BlockRef::Small(x) => !(a.pages@[x as int].object is Thread),
            _ => true,
        },
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    lemma_threads_same_caps(list_a, tables_a, list_b, tables_b, threads, a);
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_b, threads, a, t));
        let x = BlockRef::Small(t / 4096);
        assert(block_typed(a, x));
        assert(x != br);
        assert(block_refs(b, x) == block_refs(a, x));
        assert(block_dead(b, x) == block_dead(a, x));
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        assert(thread_block(a, x));
    }
}

/// The threads after a free small block is typed as something that is no thread: no thread lay in
/// it, and a thread block outside it was one before.
pub proof fn lemma_threads_small_typed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
    size: int,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        forall|k: int| 0 <= k < size ==> #[trigger] a.pages@[base + k].kind is Free,
        forall|i: int| 0 <= i < NUM_PAGES && !(base <= i < base + size) ==> #[trigger] b.pages@[i] == a.pages@[i],
        forall|k: int| 0 <= k < size ==> !((#[trigger] b.pages@[base + k]).object is Thread),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|p: usize| #[trigger] list_a.pages@.dom().contains(p) ==> list_b.pages@.dom().contains(p),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    lemma_threads_same_caps(list_a, tables_a, list_b, tables_b, threads, a);
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_b, threads, a, t));
        let x = (t / 4096) as int;
        if base <= x < base + size {
            assert(a.pages@[base + (x - base)].kind is Free);
        }
        assert(b.pages@[x] == a.pages@[x]);
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        if base <= x < base + size {
            assert(!(b.pages@[base + (x - base)].object is Thread));
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(thread_block(a, x));
    }
}

/// The threads after a small block frees: a thread's first page is the list's, so it was not in it,
/// and a freed page is no thread block.
pub proof fn lemma_threads_small_freed(
    list_a: &Tree,
    tables_a: &Tables,
    list_b: &Tree,
    tables_b: &Tables,
    threads: &Threads,
    a: &BlockTable,
    b: &BlockTable,
    base: usize,
)
    requires
        threads_wf(list_a, tables_a, threads, a),
        forall|p: usize| #[trigger] list_b.pages@.dom().contains(p) && p / 4096 < NUM_PAGES
            ==> !a.in_block(base as int, (p / 4096) as int),
        forall|i: int| 0 <= i < NUM_PAGES ==> #[trigger] b.pages@[i] == (
            if a.in_block(base as int, i) { free_entry() } else { a.pages@[i] }),
        same_threads(list_a, tables_a, list_b, tables_b),
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> list_b.pages@.dom().contains(t),
    ensures
        threads_wf(list_b, tables_b, threads, b),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies thread_wf(list_b, threads, b, t) by {
        assert(thread_wf(list_a, threads, a, t));
        assert(list_b.pages@.dom().contains(t));
        assert(!a.in_block(base as int, (t / 4096) as int));
        assert(b.pages@[(t / 4096) as int] == a.pages@[(t / 4096) as int]);
    }
    assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x) implies threads.records@.contains_key((x * 4096) as usize) by {
        if a.in_block(base as int, x as int) {
            assert(b.pages@[x as int] == free_entry());
        }
        assert(b.pages@[x as int] == a.pages@[x as int]);
        assert(thread_block(a, x));
    }
    assert forall|n: usize| #[trigger] tables_b.is_cap(list_b, n) && tables_b.payload_of(n).kind is Thread implies {
        &&& threads.records@.contains_key(tables_b.payload_of(n).base)
        &&& threads.holders@[tables_b.payload_of(n).base].contains(n)
        &&& tables_b.payload_of(n).order == THREAD_ORDER
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
    assert forall|t: usize, n: usize| threads.records@.contains_key(t) && #[trigger] threads.holders@[t].contains(n) implies {
        &&& tables_b.is_cap(list_b, n)
        &&& tables_b.payload_of(n).kind is Thread
        &&& tables_b.payload_of(n).base == t
    } by {
        assert(tables_a.is_cap(list_a, n));
    }
}

/// A thread's node page stays the list's when the page of a block of another kind leaves it.
pub proof fn lemma_thread_node_pages_kept(
    list_a: &Tree,
    list_b: &Tree,
    tables: &Tables,
    threads: &Threads,
    blocks: &BlockTable,
    base: usize,
)
    requires
        threads_wf(list_a, tables, threads, blocks),
        base / 4096 < NUM_PAGES,
        !(blocks.pages@[(base / 4096) as int].object is Thread),
        list_b.pages@.dom() == list_a.pages@.dom().remove(base),
    ensures
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> list_b.pages@.dom().contains(t),
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies list_b.pages@.dom().contains(t) by {
        assert(thread_wf(list_a, threads, blocks, t));
        assert(t != base);
    }
}

/// No thread lies in a block of another kind: a thread's first page is its own block's base.
pub proof fn lemma_threads_outside_block(list: &Tree, tables: &Tables, threads: &Threads, blocks: &BlockTable, base: usize)
    requires
        threads_wf(list, tables, threads, blocks),
        blocks.wf(),
        base < NUM_PAGES,
        blocks.pages@[base as int].kind is Base,
        !(blocks.pages@[base as int].object is Thread),
    ensures
        forall|t: usize| #[trigger] threads.records@.contains_key(t) ==> {
            &&& !blocks.in_block(base as int, (t / 4096) as int)
            &&& t % 4096 == 0
        },
{
    assert forall|t: usize| #[trigger] threads.records@.contains_key(t) implies {
        &&& !blocks.in_block(base as int, (t / 4096) as int)
        &&& t % 4096 == 0
    } by {
        assert(thread_wf(list, threads, blocks, t));
        let x = (t / 4096) as int;
        if blocks.in_block(base as int, x) && x != base {
            blocks.lemma_member_of(base as int, x);
        }
    }
}

impl CapKernel {
    /// A thread capability names a thread, whose block holds its reference, lies in no typed region
    /// and so is read as the small block at its base.
    pub proof fn lemma_thread_cap(&self, n: usize)
        requires
            self.wf(),
            self.is_cap(n),
            self.payload_of(n).kind is Thread,
        ensures
            self.threads.records@.contains_key(self.payload_of(n).base),
            self.threads.holders@[self.payload_of(n).base].contains(n),
            self.payload_of(n).base % 8192 == 0,
            self.payload_of(n).base / 4096 < NUM_PAGES,
            self.payload_of(n).order == THREAD_ORDER,
            self.blocks.pages@[(self.payload_of(n).base / 4096) as int].object is Thread,
            block_typed(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)),
            block_refs(&self.blocks, BlockRef::Small(self.payload_of(n).base / 4096)) > 0,
            block_ref(&self.blocks, self.payload_of(n).base / 4096) == BlockRef::Small(self.payload_of(n).base / 4096),
    {
        let t = self.payload_of(n).base;
        assert(self.tables.is_cap(&self.list, n));
        assert(thread_wf(&self.list, &self.threads, &self.blocks, t));
        if self.threads.holders@[t].len() == 0 {
            self.threads.holders@[t].lemma_len0_is_empty();
        }
        self.blocks.lemma_not_free_uncovered((t / 4096) as int);
    }

    /// The threads after thread capability n, the only capability that changed, joins thread t with
    /// one more reference on its block.
    pub proof fn lemma_threads_holder_added(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            !pre.is_cap(n),
            post.is_cap(n),
            post.payload_of(n).kind is Thread,
            post.payload_of(n).base == t,
            post.payload_of(n).order == THREAD_ORDER,
            pre.threads.records@.contains_key(t),
            block_refs(&pre.blocks, BlockRef::Small(t / 4096)) < usize::MAX,
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(t / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(t / 4096)) + 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(t / 4096)),
            ),
            post.threads.records == pre.threads.records,
            post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].insert(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let ha = pre.threads.holders@;
        let hb = post.threads.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(t / 4096);
        assert(thread_wf(&pre.list, &pre.threads, a, t));
        assert(!ha[t].contains(n));
        vstd::set::lemma_set_insert_len(ha[t], n);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
            implies thread_wf(&post.list, &post.threads, b, u) by {
            assert(thread_wf(&pre.list, &pre.threads, a, u));
            if u != t {
                lemma_leaf_pages_distinct(u, t);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x)
            implies post.threads.records@.contains_key((x * 4096) as usize) by {
            assert(thread_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Thread implies {
            &&& post.threads.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == THREAD_ORDER
        } by {
            if x != n {
                assert(pre.tables.is_cap(&pre.list, x));
            }
        }
        assert forall|u: usize, x: usize| post.threads.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Thread
            &&& post.tables.payload_of(x).base == u
        } by {
            if !(u == t && x == n) {
                assert(ha[u].contains(x));
                assert(pre.tables.is_cap(&pre.list, x));
                assert(x != n);
            }
        }
    }

    /// The threads after thread capability n, the only capability that changed, leaves thread t,
    /// taking its reference on the block with it.
    pub proof fn lemma_threads_holder_dropped(pre: Self, post: Self, n: usize, t: usize)
        requires
            pre.wf(),
            forall|x: usize| x != n ==> #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x),
            forall|x: usize| x != n && #[trigger] pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x),
            pre.is_cap(n),
            pre.payload_of(n).kind is Thread,
            pre.payload_of(n).base == t,
            !post.is_cap(n),
            blocks_refs_changed(
                &pre.blocks,
                &post.blocks,
                BlockRef::Small(t / 4096),
                (block_refs(&pre.blocks, BlockRef::Small(t / 4096)) - 1) as usize,
                block_dead(&pre.blocks, BlockRef::Small(t / 4096)) || block_refs(&pre.blocks, BlockRef::Small(t / 4096)) == 1,
            ),
            post.threads.records == pre.threads.records,
            post.threads.holders@ == pre.threads.holders@.insert(t, pre.threads.holders@[t].remove(n)),
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let ha = pre.threads.holders@;
        let hb = post.threads.holders@;
        let a = &pre.blocks;
        let b = &post.blocks;
        let br = BlockRef::Small(t / 4096);
        pre.lemma_thread_cap(n);
        assert(thread_wf(&pre.list, &pre.threads, a, t));
        assert(ha[t].contains(n));
        vstd::set::lemma_set_remove_len(ha[t], n);
        assert forall|u: usize| #[trigger] post.threads.records@.contains_key(u)
            implies thread_wf(&post.list, &post.threads, b, u) by {
            assert(thread_wf(&pre.list, &pre.threads, a, u));
            if u != t {
                lemma_leaf_pages_distinct(u, t);
                let x = BlockRef::Small(u / 4096);
                assert(block_typed(a, x));
                assert(x != br);
                assert(block_refs(b, x) == block_refs(a, x));
                assert(block_dead(b, x) == block_dead(a, x));
                assert(hb[u] == ha[u]);
            }
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x)
            implies post.threads.records@.contains_key((x * 4096) as usize) by {
            assert(thread_block(a, x));
        }
        assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Thread implies {
            &&& post.threads.records@.contains_key(post.tables.payload_of(x).base)
            &&& hb[post.tables.payload_of(x).base].contains(x)
            &&& post.tables.payload_of(x).order == THREAD_ORDER
        } by {
            assert(x != n);
            assert(pre.tables.is_cap(&pre.list, x));
        }
        assert forall|u: usize, x: usize| post.threads.records@.contains_key(u) && #[trigger] hb[u].contains(x) implies {
            &&& post.tables.is_cap(&post.list, x)
            &&& post.tables.payload_of(x).kind is Thread
            &&& post.tables.payload_of(x).base == u
        } by {
            assert(ha[u].contains(x));
            assert(pre.tables.is_cap(&pre.list, x));
            assert(x != n);
        }
    }

    /// What a thread's retype does to the block table: the free order-1 block at `page` is typed as the
    /// thread at `base`, its first page joins the list, and no holder changed.
    proof fn lemma_thread_blocks(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            same_mapping_nodes(&pre.list, &post.list),
            post.holders == pre.holders,
            post.zeroing == pre.zeroing,
            post.frames == pre.frames,
            post.table_pages == pre.table_pages,
            post.blocks.wf(),
            base % 8192 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page % 2 == 0,
            page + 2 <= NUM_PAGES,
            !pre.blocks.covered(page as int),
            forall|k: int| 0 <= k < 2 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.regions_2m@ == pre.blocks.regions_2m@,
            post.blocks.regions_1g@ == pre.blocks.regions_1g@,
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Thread,
            post.blocks.pages@[page as int].order == 1,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 2 ==> (#[trigger] post.blocks.pages@[page + k]).object is None,
            post.list.pages@.dom() == pre.list.pages@.dom().insert(base),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child).kind is Thread,
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
        assert forall|k: int| 0 < k < 2 implies {
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
        lemma_list_pages_used_small_typed(&pre.list, a, b, page, 2);
        lemma_list_pages_used_page_added(&pre.list, &post.list, b, base);
        lemma_holders_small_typed(&pre.list, &pre.tables, a, b, &pre.zeroing, pre.holders@, page, 1);
        lemma_holders_same_frames(&pre.list, &pre.tables, &post.list, &post.tables, b, &pre.zeroing, pre.holders@);
        assert forall|br: BlockRef| #[trigger] pre.holders@.contains_key(br) implies block_typed(a, br) by {}
        lemma_objects_small_typed(&pre.tables, &post.tables, a, b, pre.holders@, page, 2);
        lemma_leaf_blocks_small_typed(&pre.list, &pre.tables, a, b, pre.holders@, page, 2);
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
        lemma_table_pages_small_typed(&pre.list, &pre.table_pages, a, b, page, 2);
        assert forall|x: usize| x < NUM_PAGES && #[trigger] table_block(b, x)
            implies pre.table_pages.maps@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert(b.pages@[page as int].object is Thread);
            } else if page < x < page + 2 {
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

    /// The threads after a thread's retype at base: the new one has its record and node page and
    /// holds its one capability, and every other lay outside the block and keeps its holders.
    proof fn lemma_threads_thread_added(pre: Self, post: Self, base: usize, page: usize, child: usize)
        requires
            Self::space_step(pre, post, child),
            base % 8192 == 0,
            base / 4096 == page,
            page * 4096 == base,
            page + 2 <= NUM_PAGES,
            forall|k: int| 0 <= k < 2 ==> #[trigger] pre.blocks.pages@[page + k].kind is Free,
            forall|i: int| 0 <= i < NUM_PAGES && !(page <= i < page + 2) ==> #[trigger] post.blocks.pages@[i] == pre.blocks.pages@[i],
            post.blocks.pages@[page as int].kind is Base,
            post.blocks.pages@[page as int].object is Thread,
            post.blocks.pages@[page as int].order == 1,
            post.blocks.pages@[page as int].refs == 1,
            !post.blocks.pages@[page as int].dead,
            forall|k: int| 0 < k < 2 ==> (#[trigger] post.blocks.pages@[page + k]).kind is Member,
            forall|p: usize| #[trigger] pre.list.pages@.dom().contains(p) ==> post.list.pages@.dom().contains(p),
            post.list.pages@.dom().contains(base),
            post.threads.records@ == pre.threads.records@.insert(base, post.threads.records@[base]),
            post.threads.records@[base].addr() == base + THREAD_RECORD_PAGE * 4096,
            post.threads.records@[base].is_init(),
            post.threads.holders@ == pre.threads.holders@.insert(base, set![child]),
            !pre.list.nodes@[child as int].live,
            post.is_cap(child),
            post.payload_of(child) == thread_of(base),
        ensures
            threads_wf(&post.list, &post.tables, &post.threads, &post.blocks),
    {
        let a = &pre.blocks;
        let b = &post.blocks;
        let ta = &pre.threads;
        let tb = &post.threads;
        assert forall|x: usize| x != child implies {
            &&& #[trigger] post.tables.is_cap(&post.list, x) == pre.tables.is_cap(&pre.list, x)
            &&& pre.tables.is_cap(&pre.list, x) ==> post.tables.payload_of(x) == pre.tables.payload_of(x)
        } by {
            Self::lemma_space_cap_frame(pre, post, child, x);
        }
        assert(!ta.records@.contains_key(base)) by {
            if ta.records@.contains_key(base) {
                assert(thread_wf(&pre.list, ta, a, base));
                assert(a.pages@[page + 0int].kind is Free);
            }
        }
        assert(!pre.is_cap(child));
        vstd::set::lemma_set_insert_len(Set::<usize>::empty(), child);
        assert(set![child].len() == 1);
        assert forall|t: usize| #[trigger] tb.records@.contains_key(t) implies thread_wf(&post.list, tb, b, t) by {
            if t == base {
                assert(tb.holders@[base] == set![child]);
                assert(tb.holders@[base].finite());
            } else {
                assert(ta.records@.contains_key(t));
                assert(thread_wf(&pre.list, ta, a, t));
                let x = (t / 4096) as int;
                if page <= x < page + 2 {
                    assert(a.pages@[page + (x - page)].kind is Free);
                }
                assert(b.pages@[x] == a.pages@[x]);
                assert(tb.records@[t] == ta.records@[t]);
                assert(tb.holders@[t] == ta.holders@[t]);
            }
        }
        assert forall|x: usize| x < NUM_PAGES && #[trigger] thread_block(b, x) implies tb.records@.contains_key((x * 4096) as usize) by {
            if x == page {
                assert((x * 4096) as usize == base);
            } else if page < x < page + 2 {
                assert(b.pages@[page + (x - page)].kind is Member);
            } else {
                assert(b.pages@[x as int] == a.pages@[x as int]);
                assert(thread_block(a, x));
            }
        }
        assert forall|n: usize| #[trigger] post.tables.is_cap(&post.list, n) && post.tables.payload_of(n).kind is Thread implies {
            &&& tb.records@.contains_key(post.tables.payload_of(n).base)
            &&& tb.holders@[post.tables.payload_of(n).base].contains(n)
            &&& post.tables.payload_of(n).order == THREAD_ORDER
        } by {
            if n == child {
                assert(tb.holders@[base].contains(child));
            } else {
                assert(pre.tables.is_cap(&pre.list, n));
                let t = pre.tables.payload_of(n).base;
                assert(ta.records@.contains_key(t));
                assert(t != base);
                assert(tb.holders@[t] == ta.holders@[t]);
            }
        }
        assert forall|t: usize, n: usize| tb.records@.contains_key(t) && #[trigger] tb.holders@[t].contains(n) implies {
            &&& post.tables.is_cap(&post.list, n)
            &&& post.tables.payload_of(n).kind is Thread
            &&& post.tables.payload_of(n).base == t
        } by {
            if t == base {
                assert(n == child);
            } else {
                assert(ta.records@.contains_key(t));
                assert(ta.holders@[t].contains(n));
                assert(pre.tables.is_cap(&pre.list, n));
                assert(n != child);
            }
        }
    }

    /// The view of a thread's retype: one child under the untyped, naming the new thread, which no
    /// table root is, so it holds nothing.
    proof fn lemma_thread_view(pre: Self, post: Self, root: usize, from: usize, to: usize, base: usize)
        requires
            Self::adds_cap(pre, post, pre.tables.node_of(root, to)),
            pre.tables.has_slot(root, from),
            pre.tables.has_slot(root, to),
            pre.is_cap(pre.tables.node_of(root, from)),
            post.list.parent@ == pre.list.parent@.insert(pre.tables.node_of(root, to), pre.tables.node_of(root, from)),
            post.payload_of(pre.tables.node_of(root, to)) == thread_of(base),
            block_within(base, THREAD_ORDER, pre.payload_of(pre.tables.node_of(root, from))),
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
        let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
        Self::lemma_adds_node_view(pre, post, root, from, to);
        let pp = pre.payload_of(parent);
        lemma2_to64();
        assert(block_bytes(THREAD_ORDER) == 8192);
        assert(block_bytes(pp.order) == a.pages[parent] * 4096);
        assert(a.covers(parent, base)) by {
            assert(a.names.contains_key(parent));
            assert(a.pages.contains_key(parent));
            assert(a.names[parent] == pp.base);
            assert(block_within(base, THREAD_ORDER, pp));
            assert(base as int % 8192 == 0);
            vstd::arithmetic::div_mod::lemma_mod_mod(base as int, 4096, 2);
            assert(base % 4096 == 0);
            assert(base + 8192 <= pp.base + a.pages[parent] * 4096);
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

    /// Retypes the free order-1 block at `base` as a thread, under the untyped at index `from` of the
    /// table at `root`, with its capability at the empty index `to`. All of these come from user space,
    /// and a refusal changes nothing.
    pub fn retype_thread(&mut self, root: usize, from: usize, to: usize, base: usize) -> (ret: bool)
        requires
            old(self).wf(),
            old(self).tables.roots@.contains_key(root),
        ensures
            final(self).wf(),
            !ret ==> *final(self) == *old(self),
            ret ==> old(self).can_retype(root, from, to, base, THREAD_ORDER),
            ret ==> {
                let parent = old(self).tables.node_of(root, from);
                let child = old(self).tables.node_of(root, to);
                let page = (base / 4096) as int;
                &&& old(self).view().holds_right(root, parent, Right::Retype)
                &&& old(self).blocks.pages@[page].kind is Free
                &&& old(self).blocks.pages@[page + 1].kind is Free
                &&& final(self).blocks.pages@[page].kind is Base
                &&& final(self).blocks.pages@[page].object is Thread
                &&& final(self).blocks.pages@[page].order == 1
                &&& final(self).blocks.pages@[page].refs == 1
                &&& final(self).threads.records@.contains_key(base)
                &&& final(self).threads.records@[base].value() == fresh_thread()
                &&& forall|i: int| base <= i < base + NODES_PER_PAGE ==> !#[trigger] final(self).list.nodes@[i].live
                &&& final(self).view().holds(root, child)
                &&& final(self).payload_of(child) == thread_of(base)
                &&& final(self).payload_of(child).rights & right_bit(Right::Control) != 0
                &&& final(self).list.is_child(parent, child)
                &&& discharges(old(self).view(), final(self).view(), root, Effect::Retype { untyped: parent, object: base })
            },
    {
        let ghost pre = *old(self);
        let (parent, child) = match self.retype_slots(root, from, to, base, THREAD_ORDER) {
            Some(found) => found,
            None => { return false; },
        };
        if base / 4096 >= NUM_PAGES - 1 {
            return false;
        }
        let page = base / 4096;
        proof {
            lemma2_to64();
            assert(block_bytes(1) == 8192);
            assert(base % 8192 == 0);
            assert(page % 2 == 0 && page * 4096 == base) by (nonlinear_arith)
                requires
                    base % 8192 == 0,
                    page == base / 4096,
            ;
        }
        let Tracked(perms) = match self.blocks.try_type(page, 1, ObjectType::Thread) {
            Some(perms) => perms,
            None => { return false; },
        };
        let tracked mut perms = perms;
        let tracked mut first;
        let tracked second;
        proof {
            assert(0usize < order_pages(1));
            assert(1usize < order_pages(1));
            assert(perms[(page + 0usize) as usize].addr() == (page + 0usize) * 4096);
            assert(perms[(page + 1usize) as usize].addr() == (page + 1usize) * 4096);
            assert((page + 0usize) as usize == page);
            first = perms.tracked_remove(page);
            second = perms.tracked_remove((page + 1) as usize);
            // The node page's permission is ours, so no table root lies there.
            if pre.tables.roots@.contains_key(base) {
                lemma_thread_block_layouts();
                first.is_distinct(self.tables.roots.borrow().tracked_borrow(base));
                pre.tables.lemma_root(base);
            }
            assert(!pre.list.pages@.dom().contains(base)) by {
                assert(pre.blocks.pages@[page + 0int].kind is Free);
            }
            pre.lemma_slot(root, from);
            pre.lemma_slot(root, to);
            pre.lemma_slot_bound(parent);
            pre.lemma_slot_bound(child);
            pre.list.lemma_valid_bound(parent);
            pre.list.lemma_valid_bound(child);
        }
        let nodes = init_node_page(base, Tracked(first));
        self.list.add_page(base, nodes);
        let ghost mid = self.list;
        proof {
            mid.lemma_seq_fits();
            assert(mid.nodes@[parent as int] == pre.list.nodes@[parent as int]);
            assert(mid.nodes@[child as int] == pre.list.nodes@[child as int]);
        }
        let tracked mut record = page_into_thread_record(second);
        PPtr::<ThreadRecord>::from_usize(base + THREAD_RECORD_PAGE * 4096).put(Tracked(&mut record), new_thread_record());
        proof {
            self.threads.records.borrow_mut().tracked_insert(base, record);
        }
        self.list.derive(parent, child, NodeKind::Capability);
        proof {
            pre.tables.lemma_wf_same_pages(&pre.list, &self.list);
        }
        self.tables.set_payload(
            &self.list,
            root,
            to,
            Payload { kind: CapKind::Thread, order: THREAD_ORDER, rights: THREAD_RIGHTS, base, badge: 0, reserved: 0 },
        );
        self.threads.holders = Ghost(pre.threads.holders@.insert(base, set![child]));
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
            assert(post.payload_of(child) == thread_of(base));
            assert(payload_wf(post.payload_of(child)));
            assert(post.is_cap(child));
            Self::lemma_space_caps_wf(pre, post, child);
            Self::lemma_tlb_same(pre, post);
            Self::lemma_space_nodes(pre, post, mid, parent, child);
            Self::lemma_table_nodes_frame(pre, post, child, child);
            Self::lemma_space_nodes_frame(pre, post, child, child);
            lemma_mapping_nodes_grown(pre.list, mid, post.list, child, child);
            assert(post.list.pages@.dom() == pre.list.pages@.dom().insert(base));
            assert forall|k: int| 0 < k < 2 implies (#[trigger] post.blocks.pages@[page + k]).kind is Member by {
                post.blocks.lemma_member_of(page as int, page + k);
            }
            Self::lemma_thread_blocks(pre, post, base, page, child);
            assert forall|k: int| 0 <= k < 2 implies !((#[trigger] post.blocks.pages@[page + k]).object is Space) by {
                if k == 0 {
                    assert(post.blocks.pages@[page as int].object is Thread);
                }
            }
            assert forall|x: usize| #[trigger] post.tables.is_cap(&post.list, x) && post.tables.payload_of(x).kind is Space implies {
                &&& pre.tables.is_cap(&pre.list, x)
                &&& pre.tables.payload_of(x) == post.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            assert forall|x: usize| #[trigger] pre.tables.is_cap(&pre.list, x) && pre.tables.payload_of(x).kind is Space implies {
                &&& post.tables.is_cap(&post.list, x)
                &&& post.tables.payload_of(x) == pre.tables.payload_of(x)
            } by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            lemma_spaces_small_typed(&pre.list, &pre.tables, &post.list, &post.tables, &pre.spaces, &pre.blocks, &post.blocks, page, 2);
            Self::lemma_threads_thread_added(pre, post, base, page, child);
            assert forall|n: usize| #[trigger] pre.mappings@.contains_key(n)
                implies post.list.parent@.contains_key(n) && post.list.parent@[n] == pre.list.parent@[n] by {
                pre.lemma_mapping_node(n);
            }
            assert forall|x: usize| #[trigger] pre.is_cap(x) implies post.is_cap(x) && post.payload_of(x) == pre.payload_of(x) by {
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_mappings_grown(pre, post, page, 1);
            assert forall|x: usize| #[trigger] post.is_cap(x) && post.payload_of(x).kind is Device
                implies pre.is_cap(x) && pre.payload_of(x) == post.payload_of(x) by {
                assert(x != child);
                Self::lemma_space_cap_frame(pre, post, child, x);
            }
            Self::lemma_devices_same_caps(pre, post);
            assert(post.wf());
            assert forall|i: int| base <= i < base + NODES_PER_PAGE implies !#[trigger] post.list.nodes@[i].live by {
                assert(mid.valid(i as usize));
                assert(!mid.nodes@[i].live);
                assert(i != child) by {
                    assert(pre.list.valid(child));
                }
            }
            assert(THREAD_RIGHTS & 128 != 0) by (compute_only);
            assert(right_bit(Right::Control) == 128);
            assert(right_bit(Right::Retype) == 8);
            assert(post.list.parent@ == pre.list.parent@.insert(child, parent));
            Self::lemma_thread_view(pre, post, root, from, to, base);
            let live = |x: NodeId| x < NODE_SPACE && pre.list.nodes@[x as int].live;
            assert(pre.view().holds_right(root, parent, Right::Retype));
            lemma_adds_object_discharges_retype(pre.view(), post.view(), root, parent, child, live, base);
        }
        true
    }
}

} // verus!
