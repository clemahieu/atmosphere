// SPDX-License-Identifier: MIT

//! switch_thread at an unchanged idle core whose register already names the arriving thread's space.
//! The clauses about that space hold, and the arriving thread is still runnable and not current.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/switch.rs	switch_thread	returns
//! refused: unchanged: post.cores@[c as int].current_thread == next
//! refused: unchanged: match next {

use vstd::prelude::*;

verus! {

use crate::arch::{FrameKind, Registers};
use crate::capability::kernel::CapKernel;

impl super::SwitchThreadReturns for () {
    proof fn unchanged(pre: CapKernel, post: CapKernel, c: usize, frame: Registers, saved: FrameKind, next: Option<usize>, kernel_root: usize) {}
}

} // verus!
