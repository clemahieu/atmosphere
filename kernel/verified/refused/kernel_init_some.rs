// SPDX-License-Identifier: MIT

//! kernel_init's Some meets no unchanged kernel. The free runs and the image are a success case, so
//! the refusal biconditional holds, and the returned counts are not a booted kernel's. The tracked
//! pages and the block disjointness are the caller's; the claim is the postcondition on the kernel.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/capability/boot_kernel.rs	kernel_init	Some
//! refused: unchanged: ret matches Some((untyped, frame)) ==> post.booted(root, process, leaf, frames, t, free, image, untyped, frame, present, kernel_root)

use vstd::prelude::*;

verus! {

use crate::capability::boot_image::ImageRun;
use crate::capability::kernel::CapKernel;

impl super::KernelInitSome for () {
    proof fn unchanged(
        pre: CapKernel,
        post: CapKernel,
        root: usize,
        process: usize,
        leaf: usize,
        frames: usize,
        t: usize,
        free: Seq<(usize, usize)>,
        image: Seq<ImageRun>,
        present: Seq<bool>,
        kernel_root: usize,
        ret: Option<(usize, usize)>,
    ) {
    }
}

} // verus!
