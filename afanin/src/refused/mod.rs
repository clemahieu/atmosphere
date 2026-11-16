// SPDX-License-Identifier: MIT

//! False claims for the fan-in scan. A query is the other result from the state that gives one,
//! on an unchanged component. Idle is every ring having nothing available; Ready is the first ring
//! that has a slot. The specification is the trait and the body is the module, so the refusal's
//! body span is the module's, which is the span the check joins to the clause.
//! tools/check-refused.py runs each module under cfg(refused), which nothing else sets, so the
//! claims are in no image and no verify count. design/refused-claim-per-way/.

pub mod scan_idle;
pub mod scan_ready;

use vstd::prelude::*;

use aring::Consumer;

use crate::{examined, idle, ready, Heads, Scan};

verus! {

/// `scan`'s Idle where every ring has nothing available and a loadable head leaves the ring as it
/// was, claimed as Ready. The rings are unchanged, which is that state's own post.
pub trait ScanIdle {
    proof fn wrong<H: Heads>(pre: Seq<Consumer>, post: Seq<Consumer>, heads: &H, start: usize, r: Scan)
        requires
            start < pre.len(),
            forall|j: int| 0 <= j < pre.len() ==> #[trigger] pre[j].wf(),
            post == pre,
            forall|j: int| 0 <= j < pre.len() ==> #[trigger] pre[j].avail() == 0,
            forall|j: int, h: u32|
                0 <= j < pre.len() && #[trigger] heads.may_load(j, h) ==> examined(pre[j], pre[j], h),
            r is Ready,
        ensures
            ready(pre, post, (r->Ready_1)@, start as int, (r->Ready_0) as int),
    ;
}

/// `scan`'s Ready where the ring at `start` already has a slot, claimed as Idle. The rings are
/// unchanged, which is that state's own post: the scan returns before it loads a head.
pub trait ScanReady {
    proof fn wrong<H: Heads>(pre: Seq<Consumer>, post: Seq<Consumer>, heads: &H, start: usize, r: Scan)
        requires
            start < pre.len(),
            forall|j: int| 0 <= j < pre.len() ==> #[trigger] pre[j].wf(),
            post == pre,
            pre[start as int].avail() > 0,
            r is Idle,
        ensures
            idle(pre, post, (r->Idle_0)@),
    ;
}

} // verus!
