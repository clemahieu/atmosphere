// SPDX-License-Identifier: MIT

//! CoreBridge::serve's true at an unchanged server token.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/core_bridge.rs	CoreBridge::serve	true
//! refused: unchanged: post_srv.seq() == next_seq(pre_srv.seq())

use vstd::prelude::*;

verus! {

use crate::core_bridge::{ChannelOp, CoreBridge, Srv};

impl super::CoreBridgeServe for () {
    proof fn unchanged<T, Op: ChannelOp<T>>(bridge: &CoreBridge<T, Op>, cpu: usize, pre_srv: Srv<T, Op>, post_srv: Srv<T, Op>, served: bool) {}
}

} // verus!
