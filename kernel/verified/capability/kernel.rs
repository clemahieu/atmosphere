//! The capability kernel's state, which each later module extends. `wf` holds at every step boundary:
//! a long operation returns to the caller between steps, so other cores interleave only where it
//! holds. One lock covers all of this. Per-CPU state outside the lock (stacks, the GDT and TSS and the
//! switch decision) lives in kernel/src's Cpu. See the design on atmo-6x9.6.7, sections 7, 9 and 10.
use vstd::prelude::*;

verus! {

use crate::array::Array;
use crate::capability::list::*;
use crate::define::*;
use crate::pptr::PointsTo;

/// One core's view under the lock.
#[derive(Clone, Copy)]
pub struct CoreState {
    /// Only this core writes it. A stop from elsewhere is a request this core acts on.
    pub current_thread: Option<usize>,
    /// The flush epoch this core has acknowledged.
    pub acked_epoch: usize,
}

/// What a flush of every context on `core`, started when the epoch was `epoch`, proves. Only flush
/// glue can make one, so only it can clear the TLB model. That glue comes with the IPIs,
/// atmo-6x9.5.13.
pub tracked struct Flushed {
    pub ghost core: int,
    pub ghost epoch: int,
}

pub struct CapKernel {
    pub list: Tree,
    pub cores: Array<CoreState, NUM_CPUS>,
    pub flush_epoch: usize,
    /// For each core, the frames it may still hold a translation to, cached or in use.
    pub tlb: Ghost<Seq<Set<usize>>>,
    /// Frames some address space maps.
    pub mapped: Ghost<Set<usize>>,
    /// The epoch of a frame's last unmap. Page metadata holds this concretely, atmo-6x9.16.5.
    pub stale_epoch: Ghost<Map<usize, int>>,
}

impl CapKernel {
    pub open spec fn acked(&self, c: int) -> int {
        self.cores@[c].acked_epoch as int
    }

    /// A translation to an unmapped frame can survive on a core only if that core has not yet
    /// acknowledged the frame's unmap. The strict comparison needs unmap to bump the epoch first.
    pub open spec fn tlb_wf(&self) -> bool {
        &&& self.tlb@.len() == NUM_CPUS
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> #[trigger] self.acked(c) <= self.flush_epoch
        &&& forall|c: int, f: usize|
            0 <= c < NUM_CPUS && #[trigger] self.tlb@[c].contains(f) && !self.mapped@.contains(f)
            ==> self.stale_epoch@.contains_key(f) && self.acked(c) < self.stale_epoch@[f]
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.list.wf()
        &&& self.cores.wf()
        &&& self.tlb_wf()
    }

    /// No core can reach f through a stale translation. What retype needs, as a fact it can check:
    /// see lemma_acknowledged_is_clean.
    pub open spec fn no_stale_translation(&self, f: usize) -> bool {
        forall|c: int| 0 <= c < NUM_CPUS ==> !#[trigger] self.tlb@[c].contains(f)
    }

    /// Every core has acknowledged f's last unmap.
    pub open spec fn acknowledged(&self, f: usize) -> bool {
        &&& self.stale_epoch@.contains_key(f)
        &&& forall|c: int| 0 <= c < NUM_CPUS ==> self.stale_epoch@[f] <= #[trigger] self.acked(c)
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

    /// An unmapped frame every core has acknowledged is free of stale translations.
    pub proof fn lemma_acknowledged_is_clean(&self, f: usize)
        requires
            self.wf(),
            !self.mapped@.contains(f),
            self.acknowledged(f),
        ensures
            self.no_stale_translation(f),
    {
        assert forall|c: int| 0 <= c < NUM_CPUS implies !#[trigger] self.tlb@[c].contains(f) by {
            if self.tlb@[c].contains(f) {
                assert(self.acked(c) < self.stale_epoch@[f]);
                assert(self.stale_epoch@[f] <= self.acked(c));
            }
        }
    }

    /// A new kernel with one root capability, no mappings and no core running anything.
    pub fn new(root: usize, Tracked(perm): Tracked<PointsTo<NodePage>>) -> (ret: Self)
        requires
            root % 4096 == 0,
            root + 4096 <= NODE_SPACE,
            perm.addr() == root,
            perm.is_init(),
            perm.value().nodes.wf(),
            forall|k: int| 0 <= k < NODES_PER_PAGE ==> !(#[trigger] perm.value().nodes@[k]).live,
        ensures
            ret.wf(),
            ret.flush_epoch == 0,
            ret.mapped@ == Set::<usize>::empty(),
            forall|c: int| 0 <= c < NUM_CPUS ==> (#[trigger] ret.cores@[c]).current_thread.is_None(),
    {
        let list = Tree::new(root, Tracked(perm));
        let mut cores = Array::<CoreState, NUM_CPUS>::new();
        let mut i = 0;
        while i != NUM_CPUS
            invariant
                0 <= i <= NUM_CPUS,
                cores.wf(),
                forall|c: int| 0 <= c < i ==> {
                    &&& (#[trigger] cores@[c]).current_thread.is_None()
                    &&& cores@[c].acked_epoch == 0
                },
            decreases NUM_CPUS - i,
        {
            cores.set(i, CoreState { current_thread: None, acked_epoch: 0 });
            i = i + 1;
        }
        let ghost tlb = Seq::new(NUM_CPUS as nat, |c: int| Set::<usize>::empty());
        let ret = Self {
            list,
            cores,
            flush_epoch: 0,
            tlb: Ghost(tlb),
            mapped: Ghost(Set::empty()),
            stale_epoch: Ghost(Map::empty()),
        };
        ret
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

    /// Core c loaded a space that maps f, so it may now hold a translation to it.
    pub fn note_loaded(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).mapped@.contains(f),
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).tlb@[c as int].contains(f),
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
    {
        let ghost pre = *old(self);
        self.tlb = Ghost(self.tlb@.update(c as int, self.tlb@[c as int].insert(f)));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|d: int, g: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) && !self.mapped@.contains(g)
                implies self.stale_epoch@.contains_key(g) && self.acked(d) < self.stale_epoch@[g] by {
                if d == c as int {
                    assert(g != f);
                    assert(pre.tlb@[d].contains(g));
                } else {
                    assert(self.tlb@[d] == pre.tlb@[d]);
                }
                assert(pre.acked(d) == self.acked(d));
            }
        }
    }

    /// A new mapping of f exists.
    pub fn note_mapped(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).mapped@ == old(self).mapped@.insert(f),
            final(self).tlb == old(self).tlb,
            final(self).stale_epoch == old(self).stale_epoch,
            final(self).flush_epoch == old(self).flush_epoch,
    {
        let ghost pre = *old(self);
        self.mapped = Ghost(self.mapped@.insert(f));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|d: int, g: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(g) && !self.mapped@.contains(g)
                implies self.stale_epoch@.contains_key(g) && self.acked(d) < self.stale_epoch@[g] by {
                assert(g != f);
                assert(!pre.mapped@.contains(g));
                assert(pre.tlb@[d].contains(g));
            }
        }
    }

    /// f's last mapping went. The epoch is bumped first, so no core has acknowledged this unmap yet,
    /// however recently it last flushed.
    pub fn note_unmapped(&mut self, c: usize, f: usize)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            old(self).flush_epoch < usize::MAX,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).flush_epoch == old(self).flush_epoch + 1,
            final(self).mapped@ == old(self).mapped@.remove(f),
            final(self).stale_epoch@[f] == final(self).flush_epoch,
            final(self).tlb == old(self).tlb,
    {
        let ghost pre = *old(self);
        self.flush_epoch = self.flush_epoch + 1;
        let ghost e = self.flush_epoch as int;
        self.mapped = Ghost(self.mapped@.remove(f));
        self.stale_epoch = Ghost(self.stale_epoch@.insert(f, e));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                assert(pre.acked(d) <= pre.flush_epoch);
            }
            assert forall|c2: int, g: usize|
                0 <= c2 < NUM_CPUS && #[trigger] self.tlb@[c2].contains(g) && !self.mapped@.contains(g)
                implies self.stale_epoch@.contains_key(g) && self.acked(c2) < self.stale_epoch@[g] by {
                assert(pre.acked(c2) <= pre.flush_epoch);
                assert(self.acked(c2) == pre.acked(c2));
                assert(pre.tlb@[c2].contains(g));
                if g != f {
                    assert(!pre.mapped@.contains(g));
                    assert(self.stale_epoch@[g] == pre.stale_epoch@[g]);
                } else {
                    assert(self.stale_epoch@[g] == e);
                }
            }
        }
    }

    /// Core c acknowledges a flush of every context it did. Between that flush and this call c runs
    /// no user code, since IF stays clear in the kernel, so its TLB model is empty.
    pub fn acknowledge(&mut self, c: usize, epoch: usize, Tracked(flushed): Tracked<Flushed>)
        requires
            old(self).wf(),
            c < NUM_CPUS,
            flushed.core == c,
            flushed.epoch == epoch,
            old(self).acked(c as int) <= epoch <= old(self).flush_epoch,
        ensures
            Self::step_ok(*old(self), *final(self), c as int),
            final(self).acked(c as int) == epoch,
            final(self).tlb@[c as int] == Set::<usize>::empty(),
            final(self).mapped == old(self).mapped,
            final(self).stale_epoch == old(self).stale_epoch,
    {
        let ghost pre = *old(self);
        let current_thread = self.cores.get(c).current_thread;
        self.cores.set(c, CoreState { current_thread, acked_epoch: epoch });
        self.tlb = Ghost(self.tlb@.update(c as int, Set::empty()));
        proof {
            assert forall|d: int| 0 <= d < NUM_CPUS implies #[trigger] self.acked(d) <= self.flush_epoch by {
                if d != c as int {
                    assert(self.cores@[d] == pre.cores@[d]);
                    assert(pre.acked(d) <= pre.flush_epoch);
                }
            }
            assert forall|d: int| 0 <= d < NUM_CPUS && d != c as int implies
                #[trigger] self.cores@[d].current_thread == pre.cores@[d].current_thread by {
                assert(self.cores@[d] == pre.cores@[d]);
            }
            assert forall|d: int, f: usize|
                0 <= d < NUM_CPUS && #[trigger] self.tlb@[d].contains(f) && !self.mapped@.contains(f)
                implies self.stale_epoch@.contains_key(f) && self.acked(d) < self.stale_epoch@[f] by {
                if d == c as int {
                    assert(self.tlb@[d] == Set::<usize>::empty());
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
