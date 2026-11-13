// SPDX-License-Identifier: MIT

//! Core capabilities: CPU time on a core is a capability of its own kind, which boot hands the root,
//! one per core at its top priority. A core capability carries the highest priority a thread placed
//! through it may run at, and a copy derived from it carries one no higher, so a holder can hand out
//! CPU time below its own. See design/cpu-time-as-capability/.
use vstd::prelude::*;

verus! {

#[cfg(verus_keep_ghost)]
use crate::capability::reach::*;
#[cfg(verus_keep_ghost)]
use crate::capability::table::*;
#[cfg(verus_keep_ghost)]
use crate::define::*;

/// A core capability's rights: none, the capability itself is the authority.
pub const CORE_RIGHTS: u32 = 0;

/// The capability to core c, allowing placement at priority at most `priority`.
pub open spec fn core_payload(c: int, priority: usize) -> Payload {
    Payload { kind: CapKind::Core, order: 0, rights: CORE_RIGHTS, base: core_object(c), badge: 0, priority }
}

/// o is the object of one of the first c cores.
pub open spec fn core_below(o: ObjectId, c: int) -> bool {
    &&& CORE_OBJECTS <= o < CORE_OBJECTS + c * PAGE_SZ
    &&& o % PAGE_SZ == 0
}

/// The first c + 1 cores' objects are the first c cores' and core c's.
pub proof fn lemma_core_below_step(o: ObjectId, c: int)
    requires
        0 <= c < NUM_CPUS,
    ensures
        core_below(o, c + 1) <==> (core_below(o, c) || o == core_object(c)),
{
    assert(CORE_OBJECTS % PAGE_SZ == 0) by (compute_only);
    assert(CORE_OBJECTS + NUM_CPUS * PAGE_SZ <= usize::MAX) by (compute_only);
    assert((c + 1) * PAGE_SZ == c * PAGE_SZ + PAGE_SZ) by (nonlinear_arith);
    assert(0 <= c * PAGE_SZ && c * PAGE_SZ + PAGE_SZ <= NUM_CPUS * PAGE_SZ) by (nonlinear_arith)
        requires
            0 <= c < NUM_CPUS,
            PAGE_SZ > 0,
    ;
    assert((CORE_OBJECTS + c * PAGE_SZ) % (PAGE_SZ as int) == 0) by (nonlinear_arith)
        requires
            CORE_OBJECTS % PAGE_SZ == 0,
            PAGE_SZ > 0,
            c >= 0,
    ;
    assert(core_object(c) == CORE_OBJECTS + c * PAGE_SZ);
    if CORE_OBJECTS + c * PAGE_SZ <= o < CORE_OBJECTS + c * PAGE_SZ + PAGE_SZ && o % PAGE_SZ == 0 {
        assert(o == CORE_OBJECTS + c * PAGE_SZ) by (nonlinear_arith)
            requires
                CORE_OBJECTS + c * PAGE_SZ <= o < CORE_OBJECTS + c * PAGE_SZ + PAGE_SZ,
                o % PAGE_SZ == 0,
                (CORE_OBJECTS + c * PAGE_SZ) % (PAGE_SZ as int) == 0,
                PAGE_SZ > 0,
        ;
    }
}

/// Core c's object is a page, one of the cores', past power's and every device's.
pub proof fn lemma_core_object(c: int)
    requires
        0 <= c < NUM_CPUS,
    ensures
        is_core_object(core_object(c)),
        core_object(c) % PAGE_SZ == 0,
        POWER_OBJECT < core_object(c),
{
    assert(CORE_OBJECTS % PAGE_SZ == 0) by (compute_only);
    assert((CORE_OBJECTS + c * PAGE_SZ) % (PAGE_SZ as int) == 0) by (nonlinear_arith)
        requires
            CORE_OBJECTS % PAGE_SZ == 0,
            PAGE_SZ > 0,
            c >= 0,
    ;
}

} // verus!
