// SPDX-License-Identifier: MIT

//! A verified use of the wrappers: retype a frame, derive a read-only child of it and inspect the
//! child. Its ensures is proven from the wrappers' contracts alone: when the kernel accepted the
//! retype and the derive, the inspect is accepted and says a frame of the page with the read right
//! and no other.
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use verified::capability::inspect::CAP_KIND_FRAME;
#[cfg(verus_keep_ghost)]
use verified::capability::position::*;
use verified::capability::operation::*;

use crate::memory::*;
use crate::step::*;

verus! {

/// The read right's bit, as inspect returns rights and derive takes them.
pub const RIGHT_READ: u64 = 1;

/// What inspect said of the read-only child.
pub struct Inspected {
    pub kind: u64,
    pub base: u64,
    pub order: u64,
    pub rights: u64,
}

/// Retypes the page at `base` under the untyped at index `untyped` of the caller's table as a frame
/// into the empty slot at index `frame`, derives from it a child with the read right alone into the
/// empty slot at index `child`, and inspects the child. None when the kernel refused the retype or the
/// derive; otherwise what the inspect said, which is the child the derive made.
pub fn read_only_child(caller: &mut Tracked<Caller>, untyped: u64, base: u64, frame: u64, child: u64) -> (ret: Option<Inspected>)
    requires
        old(caller)@.wf(),
        frame <= POSITION_INDEX_MASK,
        child <= POSITION_INDEX_MASK,
    ensures
        final(caller)@.wf(),
        final(caller)@.root() == old(caller)@.root(),
        ret matches Some(c) ==> c.kind == CAP_KIND_FRAME && c.base == base && c.order == 0 && c.rights == RIGHT_READ,
{
    let ghost root = caller@.root();
    if retype(caller, untyped, RETYPE_FRAME, base, frame, 0).status != STATUS_OK {
        return None;
    }
    let ghost made = caller@.kernel().table_view(root)[frame as usize];
    proof {
        lemma_own_position(frame);
        lemma_own_position(child);
        assert(made.kind is Frame && made.base == base as usize && made.order == 0);
    }
    if derive(caller, frame, child, RIGHT_READ, base, 0).status != STATUS_OK {
        return None;
    }
    proof {
        let v = caller@.kernel().table_view(root)[child as usize];
        assert(caller@.kernel().table_view(root).contains_key(child as usize));
        assert(v.kind is Frame && v.base == base as usize && v.order == 0 && v.rights == RIGHT_READ as u32);
    }
    let out = inspect(caller, child);
    proof {
        assert(out.status == STATUS_OK);
    }
    Some(Inspected { kind: out.result_1, base: out.result_2, order: out.result_3, rights: out.result_4 })
}

/// A word no wider than an index names the slot at that index of the caller's own table.
proof fn lemma_own_position(word: u64)
    requires
        word <= POSITION_INDEX_MASK,
    ensures
        spec_position(word) == Some(Position { through: None, index: word as usize }),
{
    assert(word >> 32u64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert((word >> 16u64) & 0xffffu64 == 0) by (bit_vector)
        requires
            word <= 0xffffu64;
    assert(word & 0xffffu64 == word) by (bit_vector)
        requires
            word <= 0xffffu64;
}

} // verus!
