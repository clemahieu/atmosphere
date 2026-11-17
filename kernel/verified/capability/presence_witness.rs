// SPDX-License-Identifier: MIT

//! The witness for reading which entries of one table of a space are present, and which are leaves.
//! It is a module of its own so `witness.rs` stays within the file-size bound and its shared
//! solver context does not grow with these proofs. Only Verus compiles this module, so no image
//! contains it.

use vstd::prelude::*;

verus! {

use crate::capability::boot::*;
use crate::capability::boot_image::*;
use crate::capability::boot_memory::*;
use crate::capability::boot_table::*;
use crate::capability::decompose::*;
use crate::capability::kernel::*;
use crate::capability::link::*;
use crate::capability::map::*;
use crate::capability::mapping::*;
use crate::capability::presence::*;
use crate::capability::probe::mask_bit;
use crate::capability::space::*;
use crate::capability::steps::*;
use crate::capability::table::*;
use crate::capability::witness::*;
use crate::define::*;

impl CapKernel {
    /// From the state boot leaves, the root maps a frame at entry 0 of the level 1 table under entry l4
    /// of its own space as witness_root_maps_a_frame_into_its_own_space maps it, with l4 in the lower
    /// half. Through its process capability it then reads 64 entries at each level along that path,
    /// from the one the path takes: at levels 4, 3 and 2 the first is present and names the table below,
    /// so it is no leaf, and at level 1 the first is the frame's, present. Each read answers Some and
    /// changes nothing. The use is a region map learning, from the top, which parts of a space are
    /// empty: design/region-map-reads-presence-at-the-first-call/.
    #[verifier::spinoff_prover]
    pub fn witness_root_reads_presence_down_its_path(
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
        l4: usize,
    ) -> (ret: (Option<Presence>, Option<Presence>, Option<Presence>, Option<Presence>))
        requires
            old(self).booted(root@, process, leaf@, frames@, t@, free@, image@, untyped@, frame@, present@, kernel_root@),
            image_tables_bound(image@) + 4 <= untyped_tables(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0])),
            base == cursor_block(page_block_payload(runs_blocks(free@, MAX_ORDER as nat)[0]).base, image_tables_bound(image@)),
            KERNEL_MEM_END_L4INDEX <= l4 < ENTRIES / 2,
            !image_l4(image@, l4),
        ensures
            ret.0 is Some,
            ret.1 is Some,
            ret.2 is Some,
            ret.3 is Some,
            mask_bit((ret.0->0).present, 0),
            !mask_bit((ret.0->0).leaves, 0),
            mask_bit((ret.1->0).present, 0),
            !mask_bit((ret.1->0).leaves, 0),
            mask_bit((ret.2->0).present, 0),
            !mask_bit((ret.2->0).leaves, 0),
            mask_bit((ret.3->0).present, 0),
            final(self).wf(),
    {
        hide(CapKernel::wf);
        let ghost path = SpacePath { l4, l3: 0, l2: 0, l1: 0 };
        let _ = self.witness_root_maps_a_frame_into_its_own_space(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root, base, l4);
        let ghost s1 = *self;
        let ghost a1 = tree_of(&s1.table_pages, &s1.spaces);
        let va: u64 = (l4 as u64) * (SIZE_512G as u64);
        proof {
            lemma_top_entry_address(l4);
            assert(va == (l4 * SIZE_512G) as u64);
            assert(address_path(va) == path);
            let n = s1.tables.node_of(process, ROOT_PROCESS_SLOT);
            assert(s1.can_unmap(process, ROOT_PROCESS_SLOT, SpaceKind::Process, path));
            assert(s1.payload_of(n).base == process);
            assert(walk_table(a1, process, path) is Some);
            let t3 = step(a1, process, l4)->0;
            let t2 = step(a1, t3, 0)->0;
            assert(level_table(a1, process, path, 4) == Some(process));
            assert(level_table(a1, process, path, 3) == Some(t3));
            assert(level_table(a1, process, path, 2) == Some(t2));
            assert(level_table(a1, process, path, 1) == walk_table(a1, process, path));
            assert(s1.can_read_presence(process, ROOT_PROCESS_SLOT, va, 4, 64));
            assert(s1.can_read_presence(process, ROOT_PROCESS_SLOT, va, 3, 64));
            assert(s1.can_read_presence(process, ROOT_PROCESS_SLOT, va, 2, 64));
            assert(s1.can_read_presence(process, ROOT_PROCESS_SLOT, va, 1, 64));
        }
        // A witness holds no lock, so nothing bounds its count: design/one-lock-bounded-steps/.
        let tracked mut steps = Steps::fresh();
        let top = self.presence(process, ROOT_PROCESS_SLOT, va, 4, 64, Tracked(&mut steps));
        let upper = self.presence(process, ROOT_PROCESS_SLOT, va, 3, 64, Tracked(&mut steps));
        let middle = self.presence(process, ROOT_PROCESS_SLOT, va, 2, 64, Tracked(&mut steps));
        let lowest = self.presence(process, ROOT_PROCESS_SLOT, va, 1, 64, Tracked(&mut steps));
        proof {
            let t3 = step(a1, process, l4)->0;
            let t2 = step(a1, t3, 0)->0;
            let t1 = walk_table(a1, process, path)->0;
            assert(entry_set(a1, process, l4, false) && !entry_set(a1, process, l4, true));
            assert(entry_set(a1, t3, 0, false) && !entry_set(a1, t3, 0, true));
            assert(entry_set(a1, t2, 0, false) && !entry_set(a1, t2, 0, true));
            assert(entry_set(a1, t1, 0, false));
            assert(mask_bit((top->0).present, 0));
            assert(!mask_bit((top->0).leaves, 0));
            assert(mask_bit((upper->0).present, 0));
            assert(!mask_bit((upper->0).leaves, 0));
            assert(mask_bit((middle->0).present, 0));
            assert(!mask_bit((middle->0).leaves, 0));
            assert(mask_bit((lowest->0).present, 0));
        }
        (top, upper, middle, lowest)
    }
}

} // verus!
