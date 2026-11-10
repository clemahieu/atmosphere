//! The step counter: a ghost count of the work done under the kernel's lock, so a function's
//! specification can bound it. See design/one-lock-bounded-steps/.
use vstd::prelude::*;

verus! {

/// Units of work done so far. A unit is one iteration of an exec loop, whose body, apart from what
/// its callees count, runs a number of instructions the code alone bounds: a list node read or
/// written, a table or page-table entry read or written, a 4K page zeroed, a dead waiter skipped, an
/// IPI sent. Straight-line code between loops is bounded by the code's size and is not counted. A
/// function that loops takes the counter as Tracked<&mut Steps>, adds one per iteration, and ensures
/// the count rose by at most its bound; a callee's units add to its caller's.
pub tracked struct Steps {
    pub ghost count: nat,
}

impl Steps {
    /// A counter at zero. The paths that hold the kernel's lock and boot each make one; a caller
    /// whose own work is not counted yet makes one at its call, which counts toward no bound.
    pub proof fn fresh() -> (tracked ret: Steps)
        ensures
            ret.count == 0,
    {
        Steps { count: 0 }
    }

    /// One iteration's unit.
    pub proof fn step(tracked &mut self)
        ensures
            final(self).count == old(self).count + 1,
    {
        self.count = self.count + 1;
    }
}

} // verus!
