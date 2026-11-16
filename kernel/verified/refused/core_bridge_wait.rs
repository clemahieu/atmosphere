// SPDX-License-Identifier: MIT

//! CoreBridge::wait's ensures at an unchanged requester token, still pending.
//! design/refused-claim-per-way/.
//!
//! covers: kernel/verified/core_bridge.rs	CoreBridge::wait	returns
//! refused: unchanged: post_req.idle() && Op::post(pre_req.input(), out)

use vstd::prelude::*;

verus! {

use crate::core_bridge::{ChannelOp, CoreBridge, Req};

impl super::CoreBridgeWait for () {
    proof fn unchanged<T, Op: ChannelOp<T>>(bridge: &CoreBridge<T, Op>, cpu: usize, pre_req: Req<T, Op>, post_req: Req<T, Op>, out: T) {}
}

} // verus!
