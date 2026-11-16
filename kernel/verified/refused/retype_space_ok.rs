// SPDX-License-Identifier: MIT

//! retype_space's success meets no unchanged kernel: the free block is still free, so it is not a space.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/space.rs	retype_space	true
//! refused: unchanged: ret ==> space_retyped(pre, post, root, from, to, base, kind)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;
use crate::capability::space::SpaceKind;

impl super::RetypeSpaceOk for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        root: usize,
        from: usize,
        to: usize,
        base: usize,
        kind: SpaceKind,
        ret: bool,
    ) {
    }
}

} // verus!
