// SPDX-License-Identifier: MIT

//! power_off's true at a slot that holds power, claimed at the other bool. The kernel is unchanged,
//! which is power_off's own post.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/power.rs	power_off	true
//! refused: wrong: ret == kernel.holds_power(root, i)

use vstd::prelude::*;

verus! {

use crate::capability::kernel::CapKernel;

impl super::PowerOffFalse for () {
    proof fn wrong(kernel: CapKernel, root: usize, i: usize, ret: bool) {}
}

} // verus!
