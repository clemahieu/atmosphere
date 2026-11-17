// SPDX-License-Identifier: MIT

//! The kernel step: one system call, the one point of this crate no proof reaches, system_call. Its ensures is what
//! the kernel proves of the step it takes for a thread whose call returns to it, CapKernel::enter in
//! kernel/verified: some frame carrying the operation number, the slot and the arguments passed takes
//! the kernel from the state at entry to a middle state as `invoked` says, the calling core alone then
//! catches up on the flush epoch, and the state after is well formed, with that core holding nothing
//! stale of the caller's space. The state at entry is not the one the previous call returned: other
//! steps run between, another thread's or process's call, an ancestor's revoke, another core's
//! acknowledge, and the kernel proves of each that it keeps CapKernel::rely for every process whose
//! threads did not take it, and that the rely composes. So the step says only that the entry state is
//! well formed and one the rely relates to the state the caller token last held, and the token carries
//! that entry state so the wrappers can state their contracts from it. What stays unproven is that the
//! token was the kernel's state and the caller's root when the process was handed it, that the
//! process's Rust memory (its image, stack and statics) is mapped when its first call through acall
//! enters, and that the process's threads make every call through the token. The first step through
//! the token sets `Caller::start` to that call's entry state, and later steps keep it, so no page
//! token rests on the conjured start (design/region-map-reads-presence-at-the-first-call/). The step
//! is the kernel-vouched form of design/who-vouches-for-an-unproven-claim/.
use vstd::prelude::*;

use asys::operation;
#[cfg(verus_keep_ghost)]
use verified::arch::Registers;
#[cfg(verus_keep_ghost)]
use verified::define::NUM_CPUS;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::CapKernel;
#[cfg(verus_keep_ghost)]
use verified::capability::kernel::TlbEntry;
#[cfg(verus_keep_ghost)]
use verified::capability::caller::{derived_view, view_frame, view_narrows, view_writes_space, SlotView};
#[cfg(verus_keep_ghost)]
use verified::capability::link::tree_of;
#[cfg(verus_keep_ghost)]
use verified::capability::mapping::{space_mapping, SpacePath};
use verified::capability::operation::Outcome;
#[cfg(verus_keep_ghost)]
use verified::capability::reach::Right;
#[cfg(verus_keep_ghost)]
use verified::capability::refs::{block_ref, block_refs};
#[cfg(verus_keep_ghost)]
use verified::capability::rely::same_cap;
#[cfg(verus_keep_ghost)]
use verified::capability::table::block_bytes;
#[cfg(verus_keep_ghost)]
use verified::capability::view::right_bit;
#[cfg(verus_keep_ghost)]
use verified::define::PAGE_SZ;
#[cfg(verus_keep_ghost)]
use verified::pagetable::entry::PageEntry;
#[cfg(verus_keep_ghost)]
use vstd::resource::map::{GhostMapAuth, GhostPointsTo, GhostSubmap};
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::lemma_pow2_pos;

verus! {

/// What a process knows of the kernel as it calls: the kernel's state its last call returned, the state
/// that call entered from, the root of its own table, which names the process to the kernel and
/// never changes, the kernel's state when its first call through acall entered (pinned by the first
/// step; before any step, whatever state was conjured, on the vouched claim that the process's Rust
/// memory is mapped when that first call enters), and the authorities over its page tokens and its
/// frame tokens.
/// A token: its fields are private and it has
/// no constructor and no copy, so verified code holds only the one it was handed at the process's
/// start and cannot keep an old one to call with again. Only specifications read its fields, so only
/// Verus compiles them.
pub tracked struct Caller {
    #[cfg(verus_keep_ghost)]
    ghost kernel: CapKernel,
    #[cfg(verus_keep_ghost)]
    ghost entry: CapKernel,
    #[cfg(verus_keep_ghost)]
    ghost root: usize,
    #[cfg(verus_keep_ghost)]
    ghost history: Seq<(CapKernel, CapKernel)>,
    #[cfg(verus_keep_ghost)]
    ghost start: CapKernel,
    #[cfg(verus_keep_ghost)]
    tracked pages: GhostMapAuth<SpacePath, Option<usize>>,
    #[cfg(verus_keep_ghost)]
    tracked frames: GhostMapAuth<usize, (usize, Option<SpacePath>)>,
}

/// The token for one page of the caller's own space, at a path of the space keyed at the caller's
/// root: it says which frame is mapped there, by page number, or that none is
/// (design/region-map-owns-the-address-space/). Its field is private and it has no constructor and no
/// copy: verified code outside this crate gets one only from claim, once per page, or out of a PageSet,
/// and the caller token's authority holds what every token says, so Caller::pages_wf ties each to the
/// kernel's entry.
pub tracked struct PageToken {
    #[cfg(verus_keep_ghost)]
    tracked token: GhostPointsTo<SpacePath, Option<usize>>,
}

impl PageToken {
    /// The path of the page this token is for.
    pub closed spec fn path(self) -> SpacePath {
        self.token.key()
    }

    /// The frame mapped at the page, by page number, or none.
    pub closed spec fn frame(self) -> Option<usize> {
        self.token.value()
    }

    /// The authority this token belongs to.
    pub closed spec fn id(self) -> Loc {
        self.token.id()
    }

    /// The authority holds what this token says.
    pub proof fn agree(tracked &self, tracked caller: &Caller)
        requires
            self.id() == caller.pages_id(),
        ensures
            caller.pages().contains_key(self.path()),
            caller.pages()[self.path()] == self.frame(),
    {
        self.token.agree(&caller.pages);
    }
}

/// The tokens of a set of pages of the caller's own space, held as one: for each page's path, which
/// frame is mapped there, or that none is. One empty level 4 entry covers 2^27 pages, too many to claim
/// one at a time, so claim_set issues a set at once, and a client takes one page's PageToken out of it to
/// map the page through map_own and puts it back
/// (design/region-map-reads-presence-at-the-first-call/). Like a PageToken its field is private and it
/// has no constructor and no copy, and the caller token's authority holds what it says, so no page is
/// in two sets, or in a set and a PageToken, of one caller.
pub tracked struct PageSet {
    #[cfg(verus_keep_ghost)]
    tracked tokens: GhostSubmap<SpacePath, Option<usize>>,
}

impl PageSet {
    /// What the token of each page of the set says, by the page's path.
    pub closed spec fn pages(self) -> Map<SpacePath, Option<usize>> {
        self.tokens@
    }

    /// The authority this set belongs to.
    pub closed spec fn id(self) -> Loc {
        self.tokens.id()
    }

    /// The authority holds what the set says.
    pub proof fn agree(tracked &self, tracked caller: &Caller)
        requires
            self.id() == caller.pages_id(),
        ensures
            self.pages() <= caller.pages(),
    {
        self.tokens.agree(&caller.pages);
    }

    /// Takes the token of the page at `p` out of the set.
    pub proof fn take(tracked &mut self, p: SpacePath) -> (tracked token: PageToken)
        requires
            old(self).pages().contains_key(p),
        ensures
            final(self).id() == old(self).id(),
            final(self).pages() == old(self).pages().remove(p),
            token.path() == p,
            token.frame() == old(self).pages()[p],
            token.id() == old(self).id(),
    {
        let tracked token = self.tokens.split_points_to(p);
        assert(old(self).pages()[p] == token.value());
        PageToken { token }
    }

    /// Puts a page's token back into the set, which held no token for that page.
    pub proof fn put(tracked &mut self, tracked token: PageToken)
        requires
            token.id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).pages() == old(self).pages().insert(token.path(), token.frame()),
            !old(self).pages().contains_key(token.path()),
    {
        self.tokens.combine_points_to(token.token);
    }

    /// Splits the tokens of the pages in `s` out of the set into a set of their own.
    pub proof fn split(tracked &mut self, s: Set<SpacePath>) -> (tracked part: PageSet)
        requires
            s <= old(self).pages().dom(),
        ensures
            final(self).id() == old(self).id(),
            part.id() == old(self).id(),
            final(self).pages() == old(self).pages().remove_keys(s),
            part.pages() == old(self).pages().restrict(s),
    {
        let tracked tokens = self.tokens.split(s);
        assert(self.tokens@ =~= old(self).pages().remove_keys(s));
        assert(tokens@ =~= old(self).pages().restrict(s));
        PageSet { tokens }
    }

    /// Joins another set of the same authority into this one; the two held no page in common.
    pub proof fn join(tracked &mut self, tracked other: PageSet)
        requires
            other.id() == old(self).id(),
        ensures
            final(self).id() == old(self).id(),
            final(self).pages() == old(self).pages().union_prefer_right(other.pages()),
            old(self).pages().dom().disjoint(other.pages().dom()),
    {
        self.tokens.combine(other.tokens);
    }
}

/// The token for one slot of the caller's own table holding a frame capability: it says which frame
/// page the slot held when the token was claimed, its first, and the path of the page of the caller's
/// own space it is mapped at, or that it is mapped at none (design/region-map-owns-the-address-space/).
/// Its field is private and it has no constructor and no copy: verified code outside this crate gets
/// one only from claim_frame, once per slot, and the caller token's authority holds what every token
/// says, so Caller::frames_wf ties each to the kernel's state. A slot emptied or refilled with another
/// frame leaves its token true of nothing.
pub tracked struct FrameToken {
    #[cfg(verus_keep_ghost)]
    tracked token: GhostPointsTo<usize, (usize, Option<SpacePath>)>,
}

impl FrameToken {
    /// The index of the slot of the caller's own table this token is for.
    pub closed spec fn slot(self) -> usize {
        self.token.key()
    }

    /// The first page of the frame the slot held when the token was claimed, by page number.
    pub closed spec fn frame(self) -> usize {
        self.token.value().0
    }

    /// The path of the page of the caller's own space the frame is mapped at, or none.
    pub closed spec fn page(self) -> Option<SpacePath> {
        self.token.value().1
    }

    /// The authority this token belongs to.
    pub closed spec fn id(self) -> Loc {
        self.token.id()
    }

    /// The authority holds what this token says.
    pub proof fn agree(tracked &self, tracked caller: &Caller)
        requires
            self.id() == caller.frames_id(),
        ensures
            caller.frames().contains_key(self.slot()),
            caller.frames()[self.slot()] == (self.frame(), self.page()),
    {
        self.token.agree(&caller.frames);
    }
}

/// Every page of `s`, its token saying no frame is mapped there.
pub open spec fn none_at(s: Set<SpacePath>) -> Map<SpacePath, Option<usize>> {
    Map::new(s, |p: SpacePath| None::<usize>)
}

/// Sets what the token says, and the authority with it: the own-space calls, once a step has changed
/// the entry at the token's page.
pub(crate) proof fn set_page(tracked caller: &mut Caller, tracked token: &mut PageToken, frame: Option<usize>)
    requires
        old(token).id() == old(caller).pages_id(),
    ensures
        final(caller).kernel() == old(caller).kernel(),
        final(caller).entry() == old(caller).entry(),
        final(caller).root() == old(caller).root(),
        final(caller).history() == old(caller).history(),
        final(caller).start() == old(caller).start(),
        final(caller).pages_id() == old(caller).pages_id(),
        final(caller).pages() == old(caller).pages().insert(old(token).path(), frame),
        final(caller).frames() == old(caller).frames(),
        final(caller).frames_id() == old(caller).frames_id(),
        final(token).path() == old(token).path(),
        final(token).id() == old(token).id(),
        final(token).frame() == frame,
{
    token.token.update(&mut caller.pages, frame);
    assert(caller.pages@ =~= old(caller).pages@.insert(old(token).path(), frame));
}

/// The slot at `slot` of the table at `root` in `k`, while it holds a capability that writes a space,
/// holds one naming the space keyed at `root`, the process's own. Other callers only take slots from a
/// sealed process's table (CapKernel::rely), so it stays true across their steps.
pub open spec fn slot_names_own_space(k: CapKernel, root: usize, slot: usize) -> bool {
    let v = k.table_view(root);
    v.contains_key(slot) && view_writes_space(v[slot]) ==> v[slot].base == root
}

/// The slot at `slot` of the table at `root` in `k`, while it holds a capability that writes a space,
/// holds one naming a space other than the one keyed at `root`: a process building a child, not one
/// changing itself, whose own space changes only against its page tokens
/// (design/region-map-owns-the-address-space/). It stays true across other callers' steps as
/// slot_names_own_space does.
pub open spec fn slot_names_other_space(k: CapKernel, root: usize, slot: usize) -> bool {
    let v = k.table_view(root);
    v.contains_key(slot) && view_writes_space(v[slot]) ==> v[slot].base != root
}

/// The slot at `from` of the table at `root` in `k`, while it holds a frame capability, holds one with
/// the write right, so an entry mapping its page is writable, as a page token naming the page needs.
pub open spec fn frame_slot_writes(k: CapKernel, root: usize, from: usize) -> bool {
    let v = k.table_view(root);
    v.contains_key(from) && v[from].kind is Frame ==> v[from].rights & right_bit(Right::Write) != 0
}

/// The path of the large entry that would cover the page at `p`: the same path with no level-1 index.
pub open spec fn large_path(p: SpacePath) -> SpacePath {
    SpacePath { l4: p.l4, l3: p.l3, l2: p.l2, l1: 0 }
}

/// A space's mapping `m` agrees with a page token for the page at `p` saying `frame`: no large entry
/// covers the page, none is mapped there when the token says none, and what is mapped there is the
/// frame the token names, writable, when it names one. Absent under a token that names a frame is
/// allowed, as an ancestor's revoke removes entries.
pub open spec fn page_agrees(m: IMap<SpacePath, PageEntry>, p: SpacePath, frame: Option<usize>) -> bool {
    &&& !(m.contains_key(large_path(p)) && m[large_path(p)].perm.ps)
    &&& frame is None ==> !m.contains_key(p)
    &&& frame is Some && m.contains_key(p) ==> m[p].addr == frame->0 * PAGE_SZ && m[p].perm.write
}

/// The space keyed at `root` in `k` agrees with every page token `pages` holds.
pub open spec fn pages_agree(k: CapKernel, root: usize, pages: Map<SpacePath, Option<usize>>) -> bool {
    let m = space_mapping(tree_of(&k.table_pages, &k.spaces), root);
    forall|p: SpacePath| #[trigger] pages.contains_key(p) ==> page_agrees(m, p, pages[p])
}

/// The frame token for the slot at `s` of the table at `root` in `k`, saying first page `f` and
/// mapped at `m`, agrees with `k`: while the slot holds a frame capability whose first page is `f`, no
/// other table holds a capability of `f`'s block (CapKernel::held_by), and the block's count is at
/// most one, the capability's, and one more when the token names a page, so with the capability
/// counted at most that one entry maps it.
pub open spec fn frame_agrees(k: CapKernel, root: usize, s: usize, f: usize, m: Option<SpacePath>) -> bool {
    let v = k.table_view(root);
    v.contains_key(s) && v[s].kind is Frame && view_frame(v[s], 0) == f ==> {
        let br = block_ref(&k.blocks, f);
        &&& k.held_by(br, root)
        &&& block_refs(&k.blocks, br) <= (if m is Some { 2usize } else { 1usize })
    }
}

/// The table at `root` in `k` agrees with every frame token `frames` holds.
pub open spec fn frames_agree(k: CapKernel, root: usize, frames: Map<usize, (usize, Option<SpacePath>)>) -> bool {
    forall|s: usize| #[trigger] frames.contains_key(s) ==> frame_agrees(k, root, s, frames[s].0, frames[s].1)
}

/// A mapping that only lost entries, keeping the others' values, still agrees with every token.
pub proof fn lemma_shrunk_keeps_agree(a: IMap<SpacePath, PageEntry>, b: IMap<SpacePath, PageEntry>, pages: Map<SpacePath, Option<usize>>)
    requires
        forall|p: SpacePath| #[trigger] pages.contains_key(p) ==> page_agrees(a, p, pages[p]),
        forall|p: SpacePath| #[trigger] b.contains_key(p) ==> a.contains_key(p) && b[p] == a[p],
    ensures
        forall|p: SpacePath| #[trigger] pages.contains_key(p) ==> page_agrees(b, p, pages[p]),
{
    assert forall|p: SpacePath| #[trigger] pages.contains_key(p) implies page_agrees(b, p, pages[p]) by {
        assert(page_agrees(a, p, pages[p]));
        if b.contains_key(large_path(p)) {
            assert(a.contains_key(large_path(p)));
        }
        if b.contains_key(p) {
            assert(a.contains_key(p));
        }
    }
}

impl Caller {
    /// The kernel's state the last call returned, which the rely relates to the state the next call
    /// enters from.
    pub closed spec fn kernel(self) -> CapKernel {
        self.kernel
    }

    /// The kernel's state the last call entered from.
    pub closed spec fn entry(self) -> CapKernel {
        self.entry
    }

    /// The root of the calling process's table.
    pub closed spec fn root(self) -> usize {
        self.root
    }

    /// The `(entry, post)` kernel-state pairs of every `step` taken through this token so far, in order.
    pub closed spec fn history(self) -> Seq<(CapKernel, CapKernel)> {
        self.history
    }

    /// The kernel's state when the process's first call through acall entered, pinned by that first
    /// step; before any step, the conjured start, which no page token may rest on.
    pub closed spec fn start(self) -> CapKernel {
        self.start
    }

    /// What every page token of this caller says, by the page's path.
    pub closed spec fn pages(self) -> Map<SpacePath, Option<usize>> {
        self.pages@
    }

    /// The authority the caller's page tokens belong to.
    pub closed spec fn pages_id(self) -> Loc {
        self.pages.id()
    }

    /// What every frame token of this caller says, by the index of its slot.
    pub closed spec fn frames(self) -> Map<usize, (usize, Option<SpacePath>)> {
        self.frames@
    }

    /// The authority the caller's frame tokens belong to.
    pub closed spec fn frames_id(self) -> Loc {
        self.frames.id()
    }

    /// The kernel's state is one its steps keep: every step returns one.
    pub open spec fn wf(&self) -> bool {
        self.kernel().wf()
    }

    /// The caller's process is sealed and a process, so other callers only remove entries of its
    /// space (CapKernel::rely), no page token is held before the first step pins `start`, and its
    /// space agrees with every page token.
    pub open spec fn pages_wf(&self) -> bool {
        &&& self.kernel().sealed(self.root())
        &&& self.kernel().processes.records@.contains_key(self.root())
        &&& self.history().len() == 0 ==> self.pages().dom().is_empty()
        &&& pages_agree(self.kernel(), self.root(), self.pages())
    }

    /// The caller's process is sealed and a process, so other callers only take slots from its table
    /// and raise the count of no block only it holds (CapKernel::rely), and its table agrees with every
    /// frame token.
    pub open spec fn frames_wf(&self) -> bool {
        &&& self.kernel().sealed(self.root())
        &&& self.kernel().processes.records@.contains_key(self.root())
        &&& frames_agree(self.kernel(), self.root(), self.frames())
    }

    /// Takes the authorities out for the length of a call, leaving ones with no token in their place.
    proof fn take_tokens(tracked &mut self) -> (tracked tokens: (GhostMapAuth<SpacePath, Option<usize>>, GhostMapAuth<usize, (usize, Option<SpacePath>)>))
        ensures
            tokens.0 == old(self).pages,
            tokens.1 == old(self).frames,
            final(self).kernel == old(self).kernel,
            final(self).entry == old(self).entry,
            final(self).root == old(self).root,
            final(self).history == old(self).history,
            final(self).start == old(self).start,
    {
        let tracked pages = self.pages.take();
        let tracked frames = self.frames.take();
        (pages, frames)
    }

    /// Puts back what the call left aside: the authorities and the pinned start state, which a
    /// system call does not touch, since none exists at run time.
    proof fn restore(
        tracked &mut self,
        tracked pages: GhostMapAuth<SpacePath, Option<usize>>,
        tracked frames: GhostMapAuth<usize, (usize, Option<SpacePath>)>,
        start: CapKernel,
    )
        ensures
            final(self).kernel == old(self).kernel,
            final(self).entry == old(self).entry,
            final(self).root == old(self).root,
            final(self).history == old(self).history,
            final(self).start == start,
            final(self).pages == pages,
            final(self).frames == frames,
    {
        self.pages = pages;
        self.frames = frames;
        self.start = start;
    }
}

/// From `pre` to `post`, a call kept the tokens: `history` only grows, `start` stays what it was once
/// a step is in `history` and is pinned to the first step's entry when `history` was empty, and the
/// authorities and what every page token and frame token says are as they were.
pub open spec fn tokens_kept(pre: Caller, post: Caller) -> bool {
    &&& pre.history().len() <= post.history().len()
    &&& pre.history().len() > 0 ==> post.start() == pre.start()
    &&& pre.history().len() == 0 && post.history().len() > 0 ==> post.start() == post.history()[0].0
    &&& post.pages() == pre.pages()
    &&& post.pages_id() == pre.pages_id()
    &&& post.frames() == pre.frames()
    &&& post.frames_id() == pre.frames_id()
}

/// The state a call entered from agrees with every page token, and keeps the caller's process sealed
/// and a process: the rely took it there from the state the caller token last held.
pub proof fn lemma_entry_agrees(pre: Caller, post: Caller)
    requires
        pre.pages_wf(),
        post.root() == pre.root(),
        tokens_kept(pre, post),
        CapKernel::rely(pre.kernel(), post.entry(), pre.root()),
    ensures
        post.entry().sealed(pre.root()),
        post.entry().processes.records@.contains_key(pre.root()),
        pages_agree(post.entry(), pre.root(), pre.pages()),
{
    let root = pre.root();
    lemma_shrunk_keeps_agree(
        space_mapping(tree_of(&pre.kernel().table_pages, &pre.kernel().spaces), root),
        space_mapping(tree_of(&post.entry().table_pages, &post.entry().spaces), root),
        pre.pages(),
    );
}

/// A step that only removed entries of the space at `root`, sealed and a process before it, keeps that
/// space agreeing with every page token.
pub proof fn lemma_space_kept_agrees(a: CapKernel, b: CapKernel, root: usize, pages: Map<SpacePath, Option<usize>>)
    requires
        pages_agree(a, root, pages),
        a.sealed(root),
        a.processes.records@.contains_key(root),
        CapKernel::space_kept(a, b, root),
    ensures
        pages_agree(b, root, pages),
{
    lemma_shrunk_keeps_agree(
        space_mapping(tree_of(&a.table_pages, &a.spaces), root),
        space_mapping(tree_of(&b.table_pages, &b.spaces), root),
        pages,
    );
}

/// The call returned from the state its operation left, its core alone catching up, which changes no
/// space; so when that state agrees with every page token and the process is still sealed and a
/// process, the caller token's invariant holds again.
pub proof fn lemma_returned_agrees(post: Caller, mid: CapKernel, c: int)
    requires
        pages_agree(mid, post.root(), post.pages()),
        CapKernel::flushed_step(mid, post.kernel(), c),
        post.kernel().sealed(post.root()),
        post.kernel().processes.records@.contains_key(post.root()),
        post.history().len() == 0 ==> post.pages().dom().is_empty(),
    ensures
        post.pages_wf(),
{
}

/// The calling core's catching up changes only that core's state, so `space_kept` from `entry` to
/// `mid` holds to `post`.
pub proof fn lemma_returned_space_kept(entry: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize)
    requires
        CapKernel::space_kept(entry, mid, root),
        CapKernel::flushed_step(mid, post, c),
    ensures
        CapKernel::space_kept(entry, post, root),
{
}

/// The calling core's catching up leaves every table's view and the block table unchanged, so
/// `count_kept` from `entry` to `mid` holds to `post`.
pub proof fn lemma_returned_count_kept(entry: CapKernel, mid: CapKernel, post: CapKernel, c: int, root: usize)
    requires
        CapKernel::count_kept(entry, mid, root),
        CapKernel::flushed_step(mid, post, c),
        forall|t: usize| #[trigger] post.table_view(t) == mid.table_view(t),
    ensures
        CapKernel::count_kept(entry, post, root),
{
    if entry.sealed(root) {
        assert forall|j: usize, page: usize|
            entry.table_view(root).contains_key(j) && post.table_view(root).contains_key(j)
                && entry.table_view(root)[j].kind is Frame
                && (page as int) * PAGE_SZ < block_bytes(entry.table_view(root)[j].order) implies {
                let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
                &&& #[trigger] block_ref(&post.blocks, view_frame(entry.table_view(root)[j], page)) == br
                &&& entry.held_by(br, root) ==> {
                    &&& block_refs(&post.blocks, br) <= block_refs(&entry.blocks, br)
                    &&& post.held_by(br, root)
                }
            } by {
            let br = block_ref(&entry.blocks, view_frame(entry.table_view(root)[j], page));
            assert(mid.table_view(root).contains_key(j));
            assert(block_ref(&mid.blocks, view_frame(entry.table_view(root)[j], page)) == br);
            if entry.held_by(br, root) {
                assert(mid.held_by(br, root));
                assert forall|t: usize, i: usize, p: usize|
                    t != root && post.table_view(t).contains_key(i) && post.table_view(t)[i].kind is Frame
                        && (p as int) * PAGE_SZ < block_bytes(post.table_view(t)[i].order)
                        implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[i], p)) != br by {
                    assert(mid.table_view(t).contains_key(i));
                    assert(block_ref(&mid.blocks, view_frame(mid.table_view(t)[i], p)) != br);
                }
            }
        }
    }
}

/// A step that keeps the counts of the blocks of the caller's frame capabilities (count_kept) from a
/// state where its process is sealed, and leaves in its table only slots it held, with the same
/// capability, but at `w` when `w` is some, keeps every frame token but the one at `w` agreeing.
pub proof fn lemma_frames_agree_kept(a: CapKernel, b: CapKernel, root: usize, frames: Map<usize, (usize, Option<SpacePath>)>, w: Option<usize>)
    requires
        frames_agree(a, root, frames),
        a.sealed(root),
        CapKernel::count_kept(a, b, root),
        forall|j: usize| #[trigger] b.table_view(root).contains_key(j) && w != Some(j)
            ==> a.table_view(root).contains_key(j) && same_cap(b.table_view(root)[j], a.table_view(root)[j]),
    ensures
        forall|s: usize| #[trigger] frames.contains_key(s) && w != Some(s) ==> frame_agrees(b, root, s, frames[s].0, frames[s].1),
{
    assert forall|s: usize| #[trigger] frames.contains_key(s) && w != Some(s) implies frame_agrees(b, root, s, frames[s].0, frames[s].1) by {
        let f = frames[s].0;
        let m = frames[s].1;
        let va = a.table_view(root);
        let vb = b.table_view(root);
        if vb.contains_key(s) && vb[s].kind is Frame && view_frame(vb[s], 0) == f {
            assert(va.contains_key(s) && same_cap(vb[s], va[s]));
            assert(view_frame(va[s], 0) == f);
            assert(frame_agrees(a, root, s, f, m));
            lemma_pow2_pos(va[s].order as nat);
            assert((0usize as int) * PAGE_SZ < block_bytes(va[s].order));
            assert(block_ref(&b.blocks, view_frame(va[s], 0usize)) == block_ref(&a.blocks, view_frame(va[s], 0usize)));
        }
    }
}

/// The state a call entered from keeps the caller's process sealed and agrees with every frame token:
/// the rely took it there from the state the caller token last held.
pub proof fn lemma_frames_entry_agrees(pre: Caller, post: Caller)
    requires
        pre.frames_wf(),
        CapKernel::rely(pre.kernel(), post.entry(), pre.root()),
    ensures
        post.entry().sealed(pre.root()),
        post.entry().processes.records@.contains_key(pre.root()),
        frames_agree(post.entry(), pre.root(), pre.frames()),
{
    let root = pre.root();
    lemma_frames_agree_kept(pre.kernel(), post.entry(), root, pre.frames(), None);
}

/// The calling core's catching up changes no table's view and no block, so `mid` agreeing with every
/// frame token, `post` does.
pub proof fn lemma_returned_frames_agree(mid: CapKernel, post: CapKernel, c: int, root: usize, frames: Map<usize, (usize, Option<SpacePath>)>)
    requires
        frames_agree(mid, root, frames),
        CapKernel::flushed_step(mid, post, c),
        forall|t: usize| #[trigger] post.table_view(t) == mid.table_view(t),
    ensures
        frames_agree(post, root, frames),
{
    assert forall|s: usize| #[trigger] frames.contains_key(s) implies frame_agrees(post, root, s, frames[s].0, frames[s].1) by {
        assert(post.table_view(root) == mid.table_view(root));
        assert(frame_agrees(mid, root, s, frames[s].0, frames[s].1));
        let br = block_ref(&post.blocks, frames[s].0);
        if mid.held_by(br, root) {
            assert forall|t: usize, j: usize, page: usize|
                t != root && post.table_view(t).contains_key(j) && post.table_view(t)[j].kind is Frame
                    && (page as int) * PAGE_SZ < block_bytes(post.table_view(t)[j].order)
                    implies #[trigger] block_ref(&post.blocks, view_frame(post.table_view(t)[j], page)) != br by {
                assert(post.table_view(t) == mid.table_view(t));
                assert(block_ref(&mid.blocks, view_frame(mid.table_view(t)[j], page)) != br);
            }
        }
    }
}

/// A call whose step kept the counts of the caller's blocks from the state it entered from to the
/// state it returned, and left in the caller's table only slots it held there with the same
/// capability, keeps the caller's table agreeing with every frame token, the process sealed and a
/// process.
pub proof fn lemma_frames_kept(pre: Caller, post: Caller)
    requires
        pre.frames_wf(),
        post.root() == pre.root(),
        post.frames() == pre.frames(),
        CapKernel::rely(pre.kernel(), post.entry(), pre.root()),
        CapKernel::count_kept(post.entry(), post.kernel(), pre.root()),
        post.kernel().sealed(pre.root()),
        post.kernel().processes.records@.contains_key(pre.root()),
        forall|j: usize| #[trigger] post.kernel().table_view(pre.root()).contains_key(j)
            ==> post.entry().table_view(pre.root()).contains_key(j)
                && same_cap(post.kernel().table_view(pre.root())[j], post.entry().table_view(pre.root())[j]),
    ensures
        post.frames_wf(),
{
    let root = pre.root();
    lemma_frames_entry_agrees(pre, post);
    lemma_frames_agree_kept(post.entry(), post.kernel(), root, pre.frames(), None);
}

/// Other callers' steps keep every slot that names the caller's own space naming its own space
/// while the caller's process stays sealed: CapKernel::rely removes slots only and leaves every
/// surviving slot's kind, base and rights unchanged.
pub proof fn lemma_rely_keeps_slot_names_own_space(pre: CapKernel, post: CapKernel, root: usize, slot: usize)
    requires
        pre.sealed(root),
        CapKernel::rely(pre, post, root),
        slot_names_own_space(pre, root, slot),
    ensures
        slot_names_own_space(post, root, slot),
{
    if post.table_view(root).contains_key(slot) {
        assert(same_cap(post.table_view(root)[slot], pre.table_view(root)[slot]));
    }
}

/// Across the rely to `entry` and an operation leaving only surviving slots with unchanged
/// capability fields from `entry` to `post`, every slot naming the caller's own space in `pre` still
/// does in `post`.
pub proof fn lemma_shrunk_view_keeps_slot_names_own_space(pre: CapKernel, entry: CapKernel, post: CapKernel, root: usize)
    requires
        pre.sealed(root),
        CapKernel::rely(pre, entry, root),
        forall|j: usize|
            #[trigger] post.table_view(root).contains_key(j)
                ==> entry.table_view(root).contains_key(j) && same_cap(post.table_view(root)[j], entry.table_view(root)[j]),
    ensures
        forall|s: usize| #[trigger] slot_names_own_space(pre, root, s) ==> slot_names_own_space(post, root, s),
{
    assert forall|s: usize| #[trigger] slot_names_own_space(pre, root, s) implies slot_names_own_space(post, root, s) by {
        lemma_rely_keeps_slot_names_own_space(pre, entry, root, s);
        if post.table_view(root).contains_key(s) {
            assert(same_cap(post.table_view(root)[s], entry.table_view(root)[s]));
        }
    }
}

/// Deriving from a capability that writes no space other than `root` yields a capability that writes
/// no space other than `root`.
pub(crate) proof fn lemma_derived_keeps_slot_names_own_space(v: SlotView, rights: u32, base: usize, order: u8, parent: usize, root: usize)
    requires
        view_narrows(v, rights, base, order),
        view_writes_space(v) ==> v.base == root,
    ensures
        ({
            let child = derived_view(v, rights, base, order, parent);
            view_writes_space(child) ==> child.base == root
        }),
{
    let child = derived_view(v, rights, base, order, parent);
    if view_writes_space(child) {
        let vr = v.rights;
        let rw = right_bit(Right::Write);
        let rc = right_bit(Right::Control);
        if child.kind is Space {
            assert(vr & rw != 0) by (bit_vector)
                requires
                    rights & !vr == 0u32,
                    rights & rw != 0u32;
        } else {
            assert(vr & rc != 0) by (bit_vector)
                requires
                    rights & !vr == 0u32,
                    rights & rc != 0u32;
        }
    }
}

/// Claims the token for the page at `p` of the caller's own space, saying no frame is mapped there. The
/// page had no entry, nor a large one over it, at the entry of the process's first call through
/// acall, so none of the process's Rust memory lies there, its stack, statics and image being mapped
/// when that first call enters; it has none now; a step is in the history, so `start()` is pinned
/// to that entry state and no token rests on the conjured start; and no token for it was claimed
/// before, so the token is the only one.
pub proof fn claim(tracked caller: &mut Caller, p: SpacePath) -> (tracked token: PageToken)
    requires
        old(caller).pages_wf(),
        old(caller).history().len() > 0,
        !old(caller).pages().contains_key(p),
        page_agrees(space_mapping(tree_of(&old(caller).start().table_pages, &old(caller).start().spaces), old(caller).root()), p, None),
        page_agrees(space_mapping(tree_of(&old(caller).kernel().table_pages, &old(caller).kernel().spaces), old(caller).root()), p, None),
    ensures
        final(caller).kernel() == old(caller).kernel(),
        final(caller).entry() == old(caller).entry(),
        final(caller).root() == old(caller).root(),
        final(caller).history() == old(caller).history(),
        final(caller).start() == old(caller).start(),
        final(caller).pages_id() == old(caller).pages_id(),
        final(caller).pages() == old(caller).pages().insert(p, None),
        final(caller).pages_wf(),
        final(caller).frames() == old(caller).frames(),
        final(caller).frames_id() == old(caller).frames_id(),
        token.path() == p,
        token.frame() is None,
        token.id() == final(caller).pages_id(),
{
    let tracked token = caller.pages.insert(p, None);
    let ghost m = space_mapping(tree_of(&caller.kernel.table_pages, &caller.kernel.spaces), caller.root);
    assert forall|q: SpacePath| #[trigger] caller.pages@.contains_key(q) implies page_agrees(m, q, caller.pages@[q]) by {
        if q != p {
            assert(old(caller).pages().contains_key(q));
        }
    }
    PageToken { token }
}

/// Claims the tokens of the pages at the paths in `s` of the caller's own space as one set, each saying
/// no frame is mapped there, on claim's premises for every page of the set: no entry, nor a large one
/// over it, at the entry of the process's first call through acall and now, a step in the history so
/// `start()` is that entry state, and no token claimed for any page of `s` before.
pub proof fn claim_set(tracked caller: &mut Caller, s: Set<SpacePath>) -> (tracked set: PageSet)
    requires
        old(caller).pages_wf(),
        old(caller).history().len() > 0,
        s.disjoint(old(caller).pages().dom()),
        forall|p: SpacePath| #[trigger] s.contains(p) ==> {
            &&& page_agrees(space_mapping(tree_of(&old(caller).start().table_pages, &old(caller).start().spaces), old(caller).root()), p, None)
            &&& page_agrees(space_mapping(tree_of(&old(caller).kernel().table_pages, &old(caller).kernel().spaces), old(caller).root()), p, None)
        },
    ensures
        final(caller).kernel() == old(caller).kernel(),
        final(caller).entry() == old(caller).entry(),
        final(caller).root() == old(caller).root(),
        final(caller).history() == old(caller).history(),
        final(caller).start() == old(caller).start(),
        final(caller).pages_id() == old(caller).pages_id(),
        final(caller).pages() == old(caller).pages().union_prefer_right(none_at(s)),
        final(caller).pages_wf(),
        final(caller).frames() == old(caller).frames(),
        final(caller).frames_id() == old(caller).frames_id(),
        set.pages() == none_at(s),
        set.id() == final(caller).pages_id(),
{
    assert(none_at(s).dom() == s);
    assert(old(caller).pages().dom().disjoint(s));
    let tracked tokens = caller.pages.insert_map(none_at(s));
    let ghost m = space_mapping(tree_of(&caller.kernel.table_pages, &caller.kernel.spaces), caller.root);
    assert forall|q: SpacePath| #[trigger] caller.pages@.contains_key(q) implies page_agrees(m, q, caller.pages@[q]) by {
        if s.contains(q) {
            assert(caller.pages@[q] == none_at(s)[q]);
        } else {
            assert(old(caller).pages().contains_key(q));
            assert(caller.pages@[q] == old(caller).pages()[q]);
        }
    }
    PageSet { tokens }
}

/// Claims the token for the slot at `s` of the caller's own table, saying the frame it holds is mapped
/// at no page. The slot holds a frame capability whose block no other table holds a capability of, at
/// a count of one, the capability's own, as retype's contract leaves a frame it makes; and no token
/// for the slot was claimed before, so the token is the only one.
pub proof fn claim_frame(tracked caller: &mut Caller, s: usize) -> (tracked token: FrameToken)
    requires
        old(caller).frames_wf(),
        !old(caller).frames().contains_key(s),
        old(caller).kernel().table_view(old(caller).root()).contains_key(s),
        old(caller).kernel().table_view(old(caller).root())[s].kind is Frame,
        old(caller).kernel().held_by(
            block_ref(&old(caller).kernel().blocks, view_frame(old(caller).kernel().table_view(old(caller).root())[s], 0)),
            old(caller).root(),
        ),
        block_refs(
            &old(caller).kernel().blocks,
            block_ref(&old(caller).kernel().blocks, view_frame(old(caller).kernel().table_view(old(caller).root())[s], 0)),
        ) == 1,
    ensures
        final(caller).kernel() == old(caller).kernel(),
        final(caller).entry() == old(caller).entry(),
        final(caller).root() == old(caller).root(),
        final(caller).history() == old(caller).history(),
        final(caller).start() == old(caller).start(),
        final(caller).pages() == old(caller).pages(),
        final(caller).pages_id() == old(caller).pages_id(),
        final(caller).frames_id() == old(caller).frames_id(),
        final(caller).frames() == old(caller).frames().insert(
            s,
            (view_frame(old(caller).kernel().table_view(old(caller).root())[s], 0), None),
        ),
        final(caller).frames_wf(),
        token.slot() == s,
        token.frame() == view_frame(old(caller).kernel().table_view(old(caller).root())[s], 0),
        token.page() is None,
        token.id() == final(caller).frames_id(),
{
    let ghost f = view_frame(caller.kernel.table_view(caller.root)[s], 0);
    let tracked token = caller.frames.insert(s, (f, None));
    assert forall|q: usize| #[trigger] caller.frames@.contains_key(q)
        implies frame_agrees(caller.kernel, caller.root, q, caller.frames@[q].0, caller.frames@[q].1) by {
        if q != s {
            assert(old(caller).frames().contains_key(q));
        }
    }
    FrameToken { token }
}

/// No other caller stepped on the token between `pre` and `post`: `post`'s step history extends `pre`'s,
/// `post` holds the last added step's post-state (or `pre`'s kernel when none was added), and each added
/// step entered directly from the kernel state before it.
pub open spec fn caller_alone(pre: Caller, post: Caller) -> bool {
    let n = pre.history().len() as int;
    let added = post.history().skip(n);
    &&& post.root() == pre.root()
    &&& n <= post.history().len()
    &&& post.history().take(n) == pre.history()
    &&& (if added.len() == 0 {
        post.kernel() == pre.kernel()
    } else {
        post.kernel() == added.last().1
    })
    &&& forall|k: int| 0 <= k < added.len() ==>
        (#[trigger] added[k]).0 == (if k == 0 { pre.kernel() } else { added[k - 1].1 })
}

/// The frame carries this operation number, this slot and these arguments 1 to 5 where the kernel
/// reads them.
pub open spec fn carries(frame: Registers, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> bool {
    &&& frame.operation_number() == number
    &&& frame.slot() == slot
    &&& frame.argument(1) == a1
    &&& frame.argument(2) == a2
    &&& frame.argument(3) == a3
    &&& frame.argument(4) == a4
    &&& frame.argument(5) == a5
}

/// The core a call ran on, from `pre` to `post`: it had the space keyed at `root` loaded before the
/// call and still has it after, and it returns to the thread caught up on the flush epoch, holding no
/// translation of that space to a page no space maps. What CapKernel::enter proves of the core it runs
/// on for a call that returns to the thread, whose process's space is the one keyed at that process's
/// root. design/flush-without-waiting/.
pub open spec fn returned_on(pre: CapKernel, post: CapKernel, root: usize) -> bool {
    exists|c: int| 0 <= c < NUM_CPUS && #[trigger] pre.cores@[c].space == Some(root) && returned_clean(post, root, c)
}

/// Core `c` has the space keyed at `root` loaded in `post`, has acknowledged the flush epoch,
/// cleared `tlb_dirty`, and holds no translation of that space to a page no space maps.
pub open spec fn returned_clean(post: CapKernel, root: usize, c: int) -> bool {
    &&& post.cores@[c].space == Some(root)
    &&& post.acked(c) == post.flush_epoch
    &&& post.tlb_dirty == 0
    &&& forall|d: int| 0 <= d < NUM_CPUS ==> #[trigger] post.tlb@[d] == Set::<TlbEntry>::empty()
    &&& forall|e: TlbEntry| #[trigger] post.tlb@[c].contains(e) && e.space == root ==> post.mapped@.contains(e.page)
}

/// What CapKernel::enter proves of core `c`'s step for a call by a thread of the process whose space
/// is keyed at `root`, with the operation in `frame`, that returns `out` to the thread: the core had
/// that space loaded, the operation took the kernel from `pre` to `mid` as `invoked` says with the space
/// still loaded, and then only core `c`'s state and flushed TLBs changed to `post`.
pub open spec fn entered(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome, c: int, mid: CapKernel) -> bool {
    &&& 0 <= c < NUM_CPUS
    &&& pre.cores@[c].space == Some(root)
    &&& mid.cores@[c].space == Some(root)
    &&& CapKernel::invoked(pre, mid, root, frame, out)
    &&& CapKernel::flushed_step(mid, post, c)
    &&& returned_clean(post, root, c)
}

/// The step's catching up changes nothing a contract over the caller's view reads, and the core the
/// call ran on returned clean.
pub proof fn lemma_entered(pre: CapKernel, post: CapKernel, root: usize, frame: Registers, out: Outcome, c: int, mid: CapKernel)
    requires
        entered(pre, post, root, frame, out, c, mid),
    ensures
        returned_on(pre, post, root),
        post.tlb_dirty == 0,
        forall|t: usize| #[trigger] post.table_view(t) == mid.table_view(t),
{
    assert(pre.cores@[c].space == Some(root));
}

/// Invokes the operation `number` on the capability at `slot` with arguments 1 to 5, and returns what
/// the kernel put in the status and result registers. The call enters from a well-formed state the rely
/// relates to the one the token last held, which the token now carries as its entry. When the token's
/// history was empty, this first step pins `start` to that entry state; later steps keep `start`.
/// The tokens' authorities exist only in the proof, so the call keeps them.
pub(crate) fn step(caller: &mut Tracked<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        exists|frame: Registers, c: int, mid: CapKernel|
            carries(frame, number, slot, a1, a2, a3, a4, a5)
                && #[trigger] entered(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), frame, out, c, mid),
        tokens_kept(old(caller)@, final(caller)@),
    no_unwind
{
    let ghost old_start = caller@.start;
    let ghost empty_history = caller@.history.len() == 0;
    let tracked (pages, frames) = caller.borrow_mut().take_tokens();
    let out = system_call(caller, number, slot, a1, a2, a3, a4, a5);
    let ghost called = caller@;
    proof {
        let ghost start = if empty_history { called.entry } else { old_start };
        caller.borrow_mut().restore(pages, frames, start);
        assert(caller@.kernel() == called.kernel());
        assert(caller@.entry() == called.entry());
        assert(caller@.root() == called.root());
        assert(caller@.history() == called.history());
    }
    out
}

/// The system call itself, as the kernel proves it of the step it takes for the calling thread.
// kernel: kernel/verified/capability/operation.rs CapKernel::enter
// kernel: kernel/verified/capability/rely.rs CapKernel::lemma_rely_transitive
pub(crate) assume_specification[system_call](caller: &mut Tracked<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> (out: Outcome)
    requires
        old(caller)@.wf(),
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        final(caller)@.entry().wf(),
        CapKernel::rely(old(caller)@.kernel(), final(caller)@.entry(), final(caller)@.root()),
        final(caller)@.history() == old(caller)@.history().push((final(caller)@.entry(), final(caller)@.kernel())),
        exists|frame: Registers, c: int, mid: CapKernel|
            carries(frame, number, slot, a1, a2, a3, a4, a5)
                && #[trigger] entered(final(caller)@.entry(), final(caller)@.kernel(), final(caller)@.root(), frame, out, c, mid),
    no_unwind;

} // verus!

pub(crate) fn system_call(_caller: &mut Tracked<Caller>, number: u64, slot: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64) -> Outcome {
    // The ABI's own: every operation may change the caller's address space, which no Rust value of
    // this crate's caller lives in unless it holds the permission the wrapper's contract speaks of.
    let (status, results) = unsafe { operation::invoke_returning(number, slot, [a1, a2, a3, a4, a5]) };
    Outcome { status, result_1: results[0], result_2: results[1], result_3: results[2], result_4: results[3], result_5: results[4] }
}
