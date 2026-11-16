// SPDX-License-Identifier: MIT

//! What the instruction set fixes, one implementation per target, selected by target_arch. Each
//! implementation defines the same items with the same specs, so code above this module does not know
//! which ISA it runs on. See design/arch-module/.
//!
//! The tokens the glue and the capability kernel pass are defined here, once for both targets. Their
//! fields are private to this module and its per-target submodules, so no code above it can build or
//! change one: proof code cannot write the struct, and verified code cannot call Tracked::assume_new,
//! which Verus marks external. None is Copy or Clone, so a tracked token is used once. Only the glue
//! that does what a token attests makes or changes it, but for TlbModel::grow and IotlbModel::grow, by
//! which proof code may add entries to a model of what a TLB holds, since a model that holds more
//! claims less. The one value here that is not a token is the processor report, `Processor`, below.
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::capability::kernel::TlbEntry;

verus! {

/// Core `core()`'s page-table base register: the core translates through the table whose top level is
/// at `root()`, filling its TLB under tag `tag()`, the PCID or ASID written with it. The kernel value
/// holds one for each core, made at boot for the root the loader left there, and load_translation_root
/// writes the register only through it, and it cannot be copied or made above this module, so no second
/// token for the core can stand in for it while it is kept across a later write: what it says is the
/// register's latest write.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct BaseRegister {
    #[cfg(verus_keep_ghost)]
    ghost core: int,
    #[cfg(verus_keep_ghost)]
    ghost root: usize,
    #[cfg(verus_keep_ghost)]
    ghost tag: usize,
}

impl BaseRegister {
    pub closed spec fn core(self) -> int {
        self.core
    }

    pub closed spec fn root(self) -> usize {
        self.root
    }

    pub closed spec fn tag(self) -> usize {
        self.tag
    }
}

/// The tag core `core`'s base register holds after load_translation_root writes it with `id`: `id` where
/// the core tags its TLB entries with the id written (tags_tlb), and 0 where it does not, the one tag
/// every entry it caches is then held under.
pub open spec fn tag_written(core: int, id: usize) -> usize {
    if tags_tlb(core) { id } else { 0 }
}

/// One core's piece of the TLB model: the entries core `core()` may hold and the tags, PCIDs or
/// ASIDs, it may hold entries under. Held inside [`TlbModel`] and lent out one core at a time across
/// a flush request; fields are private to `arch`, so only the arch module can build or empty one.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct CoreTlb {
    #[cfg(verus_keep_ghost)]
    ghost core: int,
    #[cfg(verus_keep_ghost)]
    ghost held: Set<TlbEntry>,
    #[cfg(verus_keep_ghost)]
    ghost tags: Set<usize>,
}

impl CoreTlb {
    pub closed spec fn core(self) -> int {
        self.core
    }

    pub closed spec fn held(self) -> Set<TlbEntry> {
        self.held
    }

    pub closed spec fn tags(self) -> Set<usize> {
        self.tags
    }

    /// This core's model becomes `held`, which holds all it held. The core number and tags are kept.
    pub proof fn grow(tracked &mut self, held: Set<TlbEntry>)
        requires
            old(self).held().subset_of(held),
        ensures
            final(self).core() == old(self).core(),
            final(self).held() == held,
            final(self).tags() == old(self).tags(),
    {
        self.held = held;
    }
}

/// What each core's TLB may hold that the kernel's model tracks: one tracked `CoreTlb` piece per
/// core, indexed by core, holding a set of entries and a set of the tags, PCIDs or ASIDs, it may
/// hold entries under. The kernel value holds the one boot makes, with every set empty. Proof code
/// may add to the sets of entries, since a model that holds more claims less; load_translation_root
/// adds the tag it writes to the core's tags; and only flush_every_context empties a core's sets, so
/// a core's model is emptied, and the tags it used freed for reuse, only by a flush of that core:
/// design/flush-without-waiting/.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct TlbModel {
    #[cfg(verus_keep_ghost)]
    ghost len: nat,
    #[cfg(verus_keep_ghost)]
    tracked pieces: Map<int, CoreTlb>,
}

impl TlbModel {
    pub closed spec fn len(self) -> nat {
        self.len
    }

    /// Whether core `c`'s piece is presently in the model (not lent out).
    pub closed spec fn has(self, c: int) -> bool {
        self.pieces.contains_key(c)
    }

    /// Every piece held in the model belongs to its own valid core index.
    pub closed spec fn pieces_wf(self) -> bool {
        forall|c: int| #[trigger] self.pieces.contains_key(c) ==> 0 <= c < self.len && self.pieces[c].core() == c
    }

    /// Every core `0 <= c < len` has its piece in the model and each belongs to its core index.
    pub closed spec fn wf(self) -> bool {
        &&& self.pieces_wf()
        &&& forall|c: int| 0 <= c < self.len ==> #[trigger] self.pieces.contains_key(c)
    }

    /// Every core `0 <= c < self.len()` has its piece when `self.wf()` holds.
    pub proof fn lemma_wf_has(self, c: int)
        requires
            self.wf(),
            0 <= c < self.len(),
        ensures
            self.has(c),
    {
    }

    /// A model whose present pieces are valid and whose cores `0..len` all have pieces is `wf()`.
    pub(in crate::arch) proof fn lemma_wf_from_pieces(self)
        requires
            self.pieces_wf(),
            forall|c: int| 0 <= c < self.len() ==> #[trigger] self.has(c),
        ensures
            self.wf(),
    {
        assert forall|c: int| 0 <= c < self.len implies #[trigger] self.pieces.contains_key(c) by {
            assert(self.has(c));
        }
    }

    pub closed spec fn spec_index(self, c: int) -> Set<TlbEntry> {
        self.pieces[c].held()
    }

    /// The tags core c may hold entries under.
    pub closed spec fn tags(self, c: int) -> Set<usize> {
        self.pieces[c].tags()
    }

    /// Takes core `c`'s piece out of the model, leaving `!final(self).has(c)` and `!final(self).wf()`.
    pub(in crate::arch) proof fn take(tracked &mut self, c: int) -> (tracked piece: CoreTlb)
        requires
            old(self).pieces_wf(),
            old(self).has(c),
        ensures
            piece.core() == c,
            piece.held() == old(self)[c],
            piece.tags() == old(self).tags(c),
            final(self).len() == old(self).len(),
            final(self).pieces_wf(),
            !final(self).has(c),
            !final(self).wf(),
            forall|d: int| d != c ==> #[trigger] final(self).has(d) == old(self).has(d),
            forall|d: int| d != c ==> #[trigger] final(self)[d] == old(self)[d],
            forall|d: int| d != c ==> #[trigger] final(self).tags(d) == old(self).tags(d),
    {
        self.pieces.tracked_remove(c)
    }

    /// Returns core `c`'s piece to the model, restoring `final(self).has(c)`.
    pub(in crate::arch) proof fn put(tracked &mut self, c: int, tracked piece: CoreTlb)
        requires
            old(self).pieces_wf(),
            0 <= c < old(self).len(),
            !old(self).has(c),
            piece.core() == c,
        ensures
            final(self).len() == old(self).len(),
            final(self).pieces_wf(),
            final(self).has(c),
            final(self)[c] == piece.held(),
            final(self).tags(c) == piece.tags(),
            forall|d: int| d != c ==> #[trigger] final(self).has(d) == old(self).has(d),
            forall|d: int| d != c ==> #[trigger] final(self)[d] == old(self)[d],
            forall|d: int| d != c ==> #[trigger] final(self).tags(d) == old(self).tags(d),
    {
        self.pieces.tracked_insert(c, piece);
    }

    proof fn grow_range(tracked pieces: &mut Map<int, CoreTlb>, held: Seq<Set<TlbEntry>>, k: int)
        requires
            0 <= k <= held.len(),
            forall|c: int| 0 <= c < held.len() ==> #[trigger] old(pieces).contains_key(c),
            forall|c: int| #[trigger] old(pieces).contains_key(c) ==> 0 <= c < held.len() && old(pieces)[c].core() == c,
            forall|c: int| k <= c < held.len() ==> old(pieces)[c].held().subset_of(#[trigger] held[c]),
        ensures
            forall|c: int| 0 <= c < held.len() ==> #[trigger] final(pieces).contains_key(c),
            forall|c: int| #[trigger] final(pieces).contains_key(c) ==> 0 <= c < held.len() && final(pieces)[c].core() == c,
            forall|c: int| 0 <= c < k ==> #[trigger] final(pieces)[c] == old(pieces)[c],
            forall|c: int| k <= c < held.len() ==> {
                &&& #[trigger] final(pieces)[c].core() == old(pieces)[c].core()
                &&& final(pieces)[c].held() == held[c]
                &&& final(pieces)[c].tags() == old(pieces)[c].tags()
            },
        decreases held.len() - k,
    {
        if k < held.len() {
            let tracked mut piece = pieces.tracked_remove(k);
            piece.grow(held[k]);
            pieces.tracked_insert(k, piece);
            let ghost mid = *pieces;
            Self::grow_range(pieces, held, k + 1);
            assert forall|c: int| 0 <= c < k implies #[trigger] final(pieces)[c] == old(pieces)[c] by {
                assert(mid[c] == old(pieces)[c]);
            }
            assert forall|c: int| k <= c < held.len() implies {
                &&& #[trigger] final(pieces)[c].core() == old(pieces)[c].core()
                &&& final(pieces)[c].held() == held[c]
                &&& final(pieces)[c].tags() == old(pieces)[c].tags()
            } by {
                if c == k {
                    assert(final(pieces)[k] == mid[k]);
                } else {
                    assert(mid[c] == old(pieces)[c]);
                }
            }
        }
    }

    /// Each core's model becomes `held`'s set for it, which holds all it held. The tags are kept.
    pub proof fn grow(tracked &mut self, held: Seq<Set<TlbEntry>>)
        requires
            old(self).wf(),
            held.len() == old(self).len(),
            forall|c: int| 0 <= c < held.len() ==> old(self)[c].subset_of(#[trigger] held[c]),
        ensures
            final(self).wf(),
            final(self).len() == old(self).len(),
            forall|c: int| #[trigger] final(self).has(c) == old(self).has(c),
            forall|c: int| 0 <= c < held.len() ==> #[trigger] final(self)[c] == held[c],
            forall|c: int| 0 <= c < held.len() ==> #[trigger] final(self).tags(c) == old(self).tags(c),
    {
        assert forall|c: int| 0 <= c < held.len() implies #[trigger] self.pieces.contains_key(c) by {
            assert(self.has(c));
        }
        assert forall|c: int| 0 <= c < held.len() implies old(self).pieces[c].held().subset_of(#[trigger] held[c]) by {
            assert(old(self)[c].subset_of(held[c]));
        }
        Self::grow_range(&mut self.pieces, held, 0);
        assert forall|c: int| 0 <= c < self.len() implies #[trigger] self.has(c) by {
            assert(self.pieces.contains_key(c));
        }
        assert forall|c: int| #[trigger] final(self).has(c) == old(self).has(c) by {
            if old(self).has(c) {
                assert(old(self).pieces.contains_key(c));
                assert(0 <= c < held.len());
            }
            if final(self).has(c) {
                assert(final(self).pieces.contains_key(c));
                assert(0 <= c < held.len());
            }
        }
        assert forall|c: int| 0 <= c < held.len() implies #[trigger] final(self)[c] == held[c] by {
            assert(self.pieces[c].core() == old(self).pieces[c].core());
        }
        assert forall|c: int| 0 <= c < held.len() implies #[trigger] final(self).tags(c) == old(self).tags(c) by {
            assert(self.pieces[c].core() == old(self).pieces[c].core());
        }
    }
}

/// Whether `targets`, a mask with bit `c` for core `c`, names core `c`.
pub open spec fn flush_target(targets: u64, c: int) -> bool {
    0 <= c < 64 && targets & (1u64 << (c as u64)) != 0
}

/// Whether flush_cores, called on core `me` with `targets`, empties core `c`'s piece of the TLB model:
/// the calling core's, each target's, and, where the flush is one broadcast that reaches every core
/// (flush_reaches_every_core), every core's.
pub open spec fn flushed(me: usize, targets: u64, c: int) -> bool {
    c == me || flush_target(targets, c) || spec_flush_reaches_every_core()
}

/// What each IOMMU's IOTLB may hold that its device spaces' tables no longer say: one set of entries per
/// IOMMU, indexed by IOMMU. The kernel value holds the one boot makes, with every set empty. Proof code
/// may add to the sets, and only invalidate_iommu_all empties one, once the IOMMU has finished the
/// invalidate, so an IOMMU's model is emptied only by an invalidate that no unmap came after:
/// design/flush-without-waiting/. It also holds the record of the commands queued in the IOMMUs'
/// rings and not yet submitted, so that record exists once, as the model does, and every store into a
/// ring updates the record the submit reads.
// Only specs read the fields, and a cargo build erases specs, so only Verus compiles them.
pub tracked struct IotlbModel {
    #[cfg(verus_keep_ghost)]
    ghost held: Seq<Set<TlbEntry>>,
    #[cfg(verus_keep_ghost)]
    tracked queued: QueuedCommands,
}

impl IotlbModel {
    pub closed spec fn len(self) -> nat {
        self.held.len()
    }

    /// The commands queued in the IOMMUs' rings since the last submit.
    pub closed spec fn queued(self) -> QueuedCommands {
        self.queued
    }

    pub closed spec fn spec_index(self, i: int) -> Set<TlbEntry> {
        self.held[i]
    }

    /// Each IOMMU's model becomes `held`'s set for it, which holds all it held.
    pub proof fn grow(tracked &mut self, held: Seq<Set<TlbEntry>>)
        requires
            held.len() == old(self).len(),
            forall|i: int| 0 <= i < held.len() ==> old(self)[i].subset_of(#[trigger] held[i]),
        ensures
            final(self).len() == old(self).len(),
            forall|i: int| 0 <= i < held.len() ==> #[trigger] final(self)[i] == held[i],
            final(self).queued() == old(self).queued(),
    {
        self.held = held;
    }
}

/// What one core's processor reports, read once in that core's boot by read_processor and kept in the
/// core's block: design/processor-report-read-once/. Its fields are private to this module, so a report
/// with a bit set comes only from that read; code above it builds only `none`, every bit clear, which
/// selects every fallback. Unlike the tokens above it is Copy: it names a fact of the processor that
/// does not change, so each caller on the core passes the same bits.
#[derive(Clone, Copy)]
pub struct Processor {
    /// INVPCID is implemented.
    invpcid: bool,
    /// The core tags its TLB entries with the PCID its base register is written with.
    pcid: bool,
    /// The indirect branch prediction barrier is implemented.
    ibpb: bool,
    /// The L1 data cache flush command is implemented.
    l1d_flush: bool,
    /// The prediction restriction instructions are implemented.
    specres: bool,
}

impl Processor {
    pub closed spec fn spec_invpcid(self) -> bool {
        self.invpcid
    }

    pub closed spec fn spec_pcid(self) -> bool {
        self.pcid
    }

    pub closed spec fn spec_ibpb(self) -> bool {
        self.ibpb
    }

    pub closed spec fn spec_l1d_flush(self) -> bool {
        self.l1d_flush
    }

    pub closed spec fn spec_specres(self) -> bool {
        self.specres
    }

    /// The report a core holds before its read: every bit clear.
    pub const fn none() -> (ret: Processor)
        ensures
            !ret.spec_invpcid(),
            !ret.spec_pcid(),
            !ret.spec_ibpb(),
            !ret.spec_l1d_flush(),
            !ret.spec_specres(),
    {
        Processor { invpcid: false, pcid: false, ibpb: false, l1d_flush: false, specres: false }
    }

    #[verifier(when_used_as_spec(spec_invpcid))]
    pub fn invpcid(self) -> (ret: bool)
        ensures
            ret == self.spec_invpcid(),
    {
        self.invpcid
    }

    #[verifier(when_used_as_spec(spec_pcid))]
    pub fn pcid(self) -> (ret: bool)
        ensures
            ret == self.spec_pcid(),
    {
        self.pcid
    }

    #[verifier(when_used_as_spec(spec_ibpb))]
    pub fn ibpb(self) -> (ret: bool)
        ensures
            ret == self.spec_ibpb(),
    {
        self.ibpb
    }

    #[verifier(when_used_as_spec(spec_l1d_flush))]
    pub fn l1d_flush(self) -> (ret: bool)
        ensures
            ret == self.spec_l1d_flush(),
    {
        self.l1d_flush
    }

    #[verifier(when_used_as_spec(spec_specres))]
    pub fn specres(self) -> (ret: bool)
        ensures
            ret == self.spec_specres(),
    {
        self.specres
    }
}

/// Whether a thread's saved frame is a full frame from an interrupt, exception or controller write,
/// or a partial copy from a system call: design/cpu-time-as-capability/ and
/// design/syscall-abi-in-registers/.
#[derive(Clone, Copy)]
pub enum FrameKind {
    /// Full saved frame: every register in `Registers` is kept and restored.
    Full,
    /// Partial copy saved at a system call: the preserved registers, return state and seven
    /// invocation positions are kept; clobbered slots are zeroed.
    Partial,
}

/// What a save of `kind` keeps of `f`, and what the resume path for `kind` restores from `f`.
pub open spec fn saved_frame(f: Registers, kind: FrameKind) -> Registers {
    match kind {
        FrameKind::Full => f,
        FrameKind::Partial => partial_frame(f),
    }
}

pub fn save_frame_of(f: Registers, kind: FrameKind) -> (ret: Registers)
    ensures
        ret == saved_frame(f, kind),
{
    match kind {
        FrameKind::Full => f,
        FrameKind::Partial => partial_frame_of(f),
    }
}

} // verus!

#[cfg(target_arch = "x86_64")]
mod x86_64;
#[cfg(target_arch = "x86_64")]
pub use x86_64::*;
#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;
